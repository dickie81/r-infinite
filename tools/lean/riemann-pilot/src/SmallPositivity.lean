import Mathlib
import FourierGap

/-! # Weil positivity on every probe, for small support: `λ₁ ≥ 1/4` for `0 < a ≤ 1/16` (round 121)

**`weilQ_ge_quarter`.** For every `0 < a ≤ 1/16` (support `δ = 2a ≤ 1/8`), every normalised probe `g`
has `Q(g) ≥ 1/4`. That is **full-space** positivity of Weil's form: every real, even, square-integrable
`g` supported in `[−a, a]`, with no finite-dimensional truncation and no orthogonality condition. The
proof is analytic. It uses no zeros of `ζ`, no RH and no numerics beyond Mathlib's bounds on `π`,
`log 2`, `√2` and `γ`.

The argument is "archimedean dominance". Below `log 2` there is no prime, and the pole term is `≥ 0`,
so `Q(g) ≥ c₀ + Far(a) + Near(g)`, where:
* **A.** `c₀ = Re ψ(¼) − log π`. The exact value `ψ(¼) = −γ − π/2 − 3 log 2` follows from Mathlib's
  `digamma_one_half`, the duplication formula `digamma_two_mul` and the reflection `digamma_one_sub`.
  Hence `c₀ ≥ −5.489`.
* **B.** `Far(a) = ∫_{u > 2a} K(u) du = log((eᵃ + 1)/(eᵃ − 1)) + π/2 − arctan(sinh a)` exactly
  (`farField_eq`, via `K = ½csch(u/2) + ½sech(u/2)`). It is `≥ 4.911` for `a ≤ 1/16`.
* **C.** `Near(g) = ∫_{(0,2a]} (1 − f)K ≥ 0.8344` for every normalised probe (`nearField_all`). This uses
  round 20's exact mode expansion with the tail level `ψ₃` and unconditional Cauchy–Schwarz caps
  `p₀ ≤ ¼`, `p_{±1} ≤ (1 + 2/π)/8`, `p_{±2} ≤ ⅛`.

**Scope.**
* Numerically (round 118's closed forms), the true `λ₁` is about `0.8` at `a = 1/16`. The pole-free form
  `Q₀` stays positive only up to `a ≈ 0.105`, and past it positivity needs the pole term. At
  `2a = log 2`, `λ₁ ≈ 1.3·10⁻³`.
* This result sits inside the range of Connes–Consani's positivity theorem (support `2a ≤ log 2`, as
  recalled, not re-checked here). What is new is a complete, checkable Lean proof on the pilot's own
  definitions. Probes are even by definition; the odd sector is not treated.
-/

open Real Filter Topology Complex MeasureTheory Set

noncomputable section

namespace Pilot1ca

/-! ## A. The constant `c₀ = Re ψ(¼) − log π` -/

theorem digamma_quarter :
    Complex.digamma (1 / 4) = -(Real.eulerMascheroniConstant : ℂ) - (π : ℂ) / 2 - 3 * Complex.log 2 := by
  have hs : ∀ m : ℕ, (2 : ℂ) * (1 / 4) ≠ -(m : ℂ) := by
    intro m h
    have := congrArg Complex.re h
    simp at this
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have h2 := Complex.digamma_two_mul hs
  have hs' : ∀ n : ℤ, (1 / 4 : ℂ) ≠ n := by
    intro n h
    have := congrArg Complex.re h
    simp at this
    have h4 : (4 : ℝ) * n = 1 := by rw [← this]; norm_num
    have : (4 : ℤ) * n = 1 := by exact_mod_cast h4
    omega
  have h1 := Complex.digamma_one_sub hs'
  have hcot : Complex.cot ((π : ℂ) * (1 / 4)) = 1 := by
    rw [show (π : ℂ) * (1 / 4) = ((π / 4 : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_cot,
      Real.cot_eq_cos_div_sin, Real.cos_pi_div_four, Real.sin_pi_div_four]
    have : Real.sqrt 2 / 2 ≠ 0 := by positivity
    rw [div_self this]; simp
  rw [hcot, mul_one] at h1
  have e1 : (2 : ℂ) * (1 / 4) = 1 / 2 := by norm_num
  have e2 : (1 / 4 : ℂ) + 1 / 2 = 1 - 1 / 4 := by norm_num
  rw [e1, e2, h1, Complex.digamma_one_half] at h2
  linear_combination -h2

theorem weilConst_eq :
    weilConst = -Real.eulerMascheroniConstant - π / 2 - 3 * Real.log 2 - Real.log π := by
  unfold weilConst
  rw [digamma_quarter]
  simp [Complex.log_re]

theorem weilConst_ge : (-5.489 : ℝ) ≤ weilConst := by
  rw [weilConst_eq]
  have hγ := Real.eulerMascheroniConstant_lt_two_thirds
  have hπ := Real.pi_lt_d4
  have hπ0 := Real.pi_gt_three
  have hl2 := Real.log_two_lt_d9
  have hlogπ : Real.log π ≤ 2 * Real.log 2 + (π / 4 - 1) := by
    have h4 : Real.log π = Real.log 4 + Real.log (π / 4) := by
      rw [← Real.log_mul (by norm_num) (by positivity)]; congr 1; ring
    have h44 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    have := Real.log_le_sub_one_of_pos (show 0 < π / 4 by positivity)
    linarith
  norm_num at hl2 hπ
  linarith

/-! ## B. The far field in closed form -/

theorem hasDerivAt_farPrim {u : ℝ} (hu : 0 < u) :
    HasDerivAt (fun v => Real.log ((Real.exp (v / 2) - 1) / (Real.exp (v / 2) + 1)) + Real.arctan (Real.sinh (v / 2)))
      (kerK u) u := by
  have hE : 1 < Real.exp (u / 2) := Real.one_lt_exp_iff.mpr (by linarith)
  have hd2 : HasDerivAt (fun v : ℝ => v / 2) (1 / 2) u := by simpa using (hasDerivAt_id u).div_const 2
  have hexp : HasDerivAt (fun v => Real.exp (v / 2)) (Real.exp (u / 2) * (1 / 2)) u := hd2.exp
  have hnum := hexp.sub_const 1
  have hden := hexp.add_const 1
  have hq := hnum.div hden (by positivity)
  have hlog := hq.log (by
    show (Real.exp (u / 2) - 1) / (Real.exp (u / 2) + 1) ≠ 0
    exact (div_pos (by linarith) (by positivity)).ne')
  have hsh0 : HasDerivAt (fun v => Real.sinh (v / 2)) (Real.cosh (u / 2) * (1 / 2)) u := hd2.sinh
  have hsh := hsh0.arctan
  convert hlog.add hsh using 1
  rw [kerK_eq hu]
  have hs : Real.sinh (u / 2) = (Real.exp (u / 2) - Real.exp (-(u / 2))) / 2 := Real.sinh_eq _
  have hc : Real.cosh (u / 2) = (Real.exp (u / 2) + Real.exp (-(u / 2))) / 2 := Real.cosh_eq _
  have hinv : Real.exp (-(u / 2)) = (Real.exp (u / 2))⁻¹ := Real.exp_neg _
  have hc2 : 1 + Real.sinh (u / 2) ^ 2 = Real.cosh (u / 2) ^ 2 := by
    have := Real.cosh_sq (u / 2); linarith
  have hE0 : Real.exp (u / 2) - 1 ≠ 0 := by linarith
  have hE1 : Real.exp (u / 2) + 1 ≠ 0 := by positivity
  have hEpos : 0 < Real.exp (u / 2) := Real.exp_pos _
  have hE2 : Real.exp (u / 2) ^ 2 - 1 ≠ 0 := by nlinarith
  have hE2' : -1 + Real.exp (u / 2) ^ 2 ≠ 0 := by nlinarith
  simp only [Pi.div_apply, hc2]
  rw [hs, hc, hinv]
  field_simp
  ring

theorem tendsto_farPrim :
    Tendsto (fun v => Real.log ((Real.exp (v / 2) - 1) / (Real.exp (v / 2) + 1)) + Real.arctan (Real.sinh (v / 2)))
      atTop (𝓝 (0 + π / 2)) := by
  have hE : Tendsto (fun v : ℝ => Real.exp (v / 2)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_id.atTop_div_const (by norm_num))
  have hq : Tendsto (fun v : ℝ => (Real.exp (v / 2) - 1) / (Real.exp (v / 2) + 1)) atTop (𝓝 1) := by
    have h2 : Tendsto (fun v : ℝ => 2 / (Real.exp (v / 2) + 1)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ 1 hE)
    have := (tendsto_const_nhds (x := (1 : ℝ))).sub h2
    rw [sub_zero] at this
    refine this.congr' (Eventually.of_forall fun v => ?_)
    have : Real.exp (v / 2) + 1 ≠ 0 := by positivity
    field_simp; ring
  have hlog : Tendsto (fun v : ℝ => Real.log ((Real.exp (v / 2) - 1) / (Real.exp (v / 2) + 1))) atTop (𝓝 0) := by
    have := ((Real.continuousAt_log one_ne_zero).tendsto).comp hq
    rw [Real.log_one] at this
    exact this
  have hsinh : Tendsto (fun v : ℝ => Real.sinh (v / 2)) atTop atTop := by
    refine tendsto_atTop_mono' atTop ?_ (tendsto_id.atTop_div_const (by norm_num : (0 : ℝ) < 2))
    filter_upwards [eventually_ge_atTop 0] with v hv
    simp only [id]
    exact Real.self_le_sinh_iff.mpr (by linarith)
  have hat := (tendsto_nhds_of_tendsto_nhdsWithin Real.tendsto_arctan_atTop).comp hsinh
  exact hlog.add hat

/-- **The far field, exactly**: `∫_{u > 2a} K(u) du = log((eᵃ + 1)/(eᵃ − 1)) + π/2 − arctan(sinh a)`. -/
theorem farField_eq {a : ℝ} (ha : 0 < a) :
    ∫ u in Ioi (2 * a), kerK u
      = -Real.log ((Real.exp a - 1) / (Real.exp a + 1)) + (π / 2 - Real.arctan (Real.sinh a)) := by
  rw [integral_Ioi_of_hasDerivAt_of_nonneg' (fun x hx => hasDerivAt_farPrim (by
      have := mem_Ici.mp hx; linarith)) (fun x hx => (kerK_pos (by
      have := mem_Ioi.mp hx; linarith)).le) tendsto_farPrim]
  rw [show 2 * a / 2 = a by ring]
  ring

/-- **The far field is at least `4.911`** for `0 < a ≤ 1/16`. -/
theorem farField_ge {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1 / 16) : (4.911 : ℝ) ≤ ∫ u in Ioi (2 * a), kerK u := by
  rw [farField_eq ha]
  have hE : 1 < Real.exp a := Real.one_lt_exp_iff.mpr ha
  have hEa : Real.exp a - 1 ≤ a * Real.exp a := by
    have h := Real.add_one_le_exp (-a)
    have : Real.exp (-a) * Real.exp a = 1 := by rw [← Real.exp_add]; simp
    nlinarith [Real.exp_pos a, Real.exp_pos (-a)]
  -- the log part: log((eᵃ+1)/(eᵃ−1)) ≥ log(2/(a eᵃ)) = log 2 − log a − a ≥ 5 log 2 − 1/16
  have hratio : 2 / (a * Real.exp a) ≤ (Real.exp a + 1) / (Real.exp a - 1) := by
    rw [div_le_div_iff₀ (by positivity) (by linarith)]
    nlinarith [Real.exp_pos a]
  have hlogr : Real.log (2 / (a * Real.exp a)) ≤ Real.log ((Real.exp a + 1) / (Real.exp a - 1)) :=
    Real.log_le_log (by positivity) hratio
  have hneg : -Real.log ((Real.exp a - 1) / (Real.exp a + 1)) = Real.log ((Real.exp a + 1) / (Real.exp a - 1)) := by
    rw [← Real.log_inv, inv_div]
  have hsplit : Real.log (2 / (a * Real.exp a)) = Real.log 2 - Real.log a - a := by
    rw [Real.log_div (by norm_num) (by positivity), Real.log_mul ha.ne' (Real.exp_pos a).ne', Real.log_exp]; ring
  have hloga : Real.log a ≤ -(4 * Real.log 2) := by
    have : Real.log a ≤ Real.log (1 / 16) := Real.log_le_log ha ha1
    rw [show (1 / 16 : ℝ) = (2 ^ 4)⁻¹ by norm_num, Real.log_inv, Real.log_pow] at this
    push_cast at this; linarith
  -- the arctan part
  have hat : Real.arctan (Real.sinh a) ≤ Real.sinh a := Real.arctan_le_self (Real.sinh_nonneg_iff.mpr ha.le)
  have hsh : Real.sinh a ≤ a + a ^ 3 / 6 + a ^ 5 / 100 := sinh_le_taylor ha.le (by linarith)
  have hl2 := Real.log_two_gt_d9
  have hπ := Real.pi_gt_d6
  have h3 : a ^ 3 ≤ (1 / 16) ^ 3 := pow_le_pow_left₀ ha.le ha1 3
  have h5 : a ^ 5 ≤ (1 / 16) ^ 5 := pow_le_pow_left₀ ha.le ha1 5
  rw [hneg]
  norm_num at hl2 hπ h3 h5 ⊢
  linarith

/-! ## C. The near field for every normalised probe -/

def lowS2 : Finset ℤ := {-2, -1, 0, 1, 2}

theorem not_mem_lowS2 {n : ℤ} (hn : n ∉ lowS2) : 3 ≤ n ∨ n ≤ -3 := by
  simp only [lowS2, Finset.mem_insert, Finset.mem_singleton, not_or] at hn
  omega

theorem sum_lowS2_even {f : ℤ → ℝ} (hf : ∀ k, f (-k) = f k) :
    ∑ n ∈ lowS2, f n = f 0 + 2 * (f 1 + f 2) := by
  simp only [lowS2]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [show (-2 : ℤ) = -(2 : ℤ) from rfl, show (-1 : ℤ) = -(1 : ℤ) from rfl, hf, hf]
  ring

/-- The tail level `τ₃ = 2.2965 − err(a)` bounds every mode `|n| ≥ 3`. -/
theorem tail3_ok {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) {n : ℤ} (hn : 3 ≤ n) : 2.2965 - errK a ≤ modeE a n := by
  have hnr : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hψ := modeE_ge ha ha1 (n := n) (by omega)
  have hC : Cin (π * 3 / 2) ≤ Cin (π * n / 2) := Cin_mono (by positivity) (by nlinarith [Real.pi_pos])
  have hc := cin_val3
  have hπ := Real.pi_gt_three
  have h1 : 2 * Real.sin (π * n / 2) / (π * n) ≤ 2 / (π * n) :=
    div_le_div_of_nonneg_right (by linarith [Real.sin_le_one (π * n / 2)]) (by positivity)
  have h2 : 2 / (π * n) ≤ 1 := by
    rw [div_le_one (by positivity)]; nlinarith
  have hD : 0 ≤ a * (1 - 2 * Real.sin (π * n / 2) / (π * n)) := mul_nonneg ha.le (by linarith)
  linarith

theorem tail3_all {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (n : ℤ) (hn : n ∉ lowS2) : 2.2965 - errK a ≤ modeE a n := by
  rcases not_mem_lowS2 hn with h | h
  · exact tail3_ok ha ha1 h
  · have e := modeE_neg a (-n)
    rw [neg_neg] at e
    rw [e]; exact tail3_ok ha ha1 (by omega)

/-- Cauchy–Schwarz cap on a mode mass: `p_n ≤ (∫_{−a}^{a} cos²(πnt/4a))/(8a)`. -/
theorem pm_cap {a : ℝ} (ha : 0 < a) {g : ℝ → ℝ} (hp : Probe a g) (hn : normSq g = 1) (n : ℤ) :
    pm a g n ≤ (∫ t in (-a)..a, Real.cos (π * n * t / (4 * a)) ^ 2) / (8 * a) := by
  rw [pm_even ha hp]
  have hcs := cs_supp ha hp (h := fun t => Real.cos (π * n * t / (4 * a))) (by fun_prop)
  rw [hn, one_mul] at hcs
  exact div_le_div_of_nonneg_right hcs (by linarith)

theorem pm_cap0 {a : ℝ} (ha : 0 < a) {g : ℝ → ℝ} (hp : Probe a g) (hn : normSq g = 1) : pm a g 0 ≤ 1 / 4 := by
  have h := pm_cap ha hp hn 0
  simp only [Int.cast_zero, mul_zero, zero_mul, zero_div, Real.cos_zero, one_pow,
    intervalIntegral.integral_const, smul_eq_mul, mul_one] at h
  calc pm a g 0 ≤ (a - -a) / (8 * a) := h
    _ = 1 / 4 := by field_simp; ring

theorem pm_cap_pos {a : ℝ} (ha : 0 < a) {g : ℝ → ℝ} (hp : Probe a g) (hn : normSq g = 1) {k : ℤ} (hk : 0 < k) :
    pm a g k ≤ (1 + 2 * Real.sin (π * k / 2) / (π * k)) / 8 := by
  have h := pm_cap ha hp hn k
  have e := integral_cos_sub_sq ha hk 0
  simp only [sub_zero, mul_zero, zero_mul, zero_div, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, add_zero] at e
  rw [e] at h
  calc pm a g k ≤ a * (1 + 2 * Real.sin (π * k / 2) / (π * k)) / (8 * a) := h
    _ = (1 + 2 * Real.sin (π * k / 2) / (π * k)) / 8 := by field_simp

theorem pm_cap1 {a : ℝ} (ha : 0 < a) {g : ℝ → ℝ} (hp : Probe a g) (hn : normSq g = 1) : pm a g 1 ≤ 0.2046 := by
  have h := pm_cap_pos ha hp hn (k := 1) (by norm_num)
  push_cast at h
  rw [show π * (1 : ℝ) / 2 = π / 2 by ring, Real.sin_pi_div_two] at h
  obtain ⟨-, b2, -⟩ := num_atoms
  have e : 2 * 1 / (π * 1) = 2 * (1 / π) := by field_simp
  rw [e] at h
  linarith

theorem pm_cap2 {a : ℝ} (ha : 0 < a) {g : ℝ → ℝ} (hp : Probe a g) (hn : normSq g = 1) : pm a g 2 ≤ 1 / 8 := by
  have h := pm_cap_pos ha hp hn (k := 2) (by norm_num)
  push_cast at h
  rw [show π * (2 : ℝ) / 2 = π by ring, Real.sin_pi] at h
  simpa using h

/-- **The near field of every normalised probe**: `∫_{(0,2a]} (1 − f)K ≥ 0.8344` for `0 < a ≤ 1/16`. -/
theorem nearField_all {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1 / 16) {g : ℝ → ℝ} (hp : Probe a g)
    (hn : normSq g = 1) : (0.8344 : ℝ) ≤ ∫ u in Ioc 0 (2 * a), archIntegrand g u := by
  set τ := 2.2965 - errK a with hτ
  have hE := energy_ge_trunc ha hp hn lowS2 (τ := τ) (tail3_all ha (by linarith))
  have hsum : ∑ n ∈ lowS2, (modeE a n - τ) * pm a g n
      = (modeE a 0 - τ) * pm a g 0
        + 2 * ((modeE a 1 - τ) * pm a g 1 + (modeE a 2 - τ) * pm a g 2) :=
    sum_lowS2_even fun k => by simp only [modeE_neg, pm_neg ha hp]
  rw [hsum] at hE
  have herr0 : 0 ≤ errK a := errK_nonneg ha.le
  have herr : errK a ≤ 0.00075 := by
    unfold errK
    have h2 : a ^ 2 ≤ (1 / 16) ^ 2 := pow_le_pow_left₀ ha.le ha1 2
    have h3 : a ^ 3 ≤ (1 / 16) ^ 3 := pow_le_pow_left₀ ha.le ha1 3
    have h4 : a ^ 4 ≤ (1 / 16) ^ 4 := pow_le_pow_left₀ ha.le ha1 4
    have h5 : a ^ 5 ≤ (1 / 16) ^ 5 := pow_le_pow_left₀ ha.le ha1 5
    norm_num at h2 h3 h4 h5 ⊢; linarith
  have t0 : (0 - τ) * (1 / 4) ≤ (modeE a 0 - τ) * pm a g 0 :=
    term_ge (le_of_eq (modeE_zero a).symm) (by rw [hτ]; linarith) (pm_nonneg ha g 0) (pm_cap0 ha hp hn)
  have t1 := term_mode ha (by linarith) (g := g) (k := 1) (by norm_num) (Cv := 0.5408) (D := 0.36338) (X := 0)
    (Y := 0) (τ := τ) (P := 0.2046) (by simpa using cin_val1) dlo1 le_rfl
    (by rw [hτ]; nlinarith) (pm_cap1 ha hp hn)
  have t2 := term_mode ha (by linarith) (g := g) (k := 2) (by norm_num) (Cv := 1.6214) (D := 1) (X := 0)
    (Y := 0) (τ := τ) (P := 1 / 8) (by simpa using cin_val2) dlo2 le_rfl
    (by rw [hτ]; nlinarith) (pm_cap2 ha hp hn)
  simp only [sub_zero] at t1 t2
  rw [hτ] at t0 t1 t2 hE
  nlinarith

/-! ## D. Positivity -/

/-- **Weil positivity on every probe at small support**: for `0 < a ≤ 1/16`, every normalised probe
has `Q(g) ≥ 1/4`. No zero of `ζ`, no RH, no finite-dimensional truncation. -/
theorem weilQ_ge_quarter {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1 / 16) {g : ℝ → ℝ} (hp : Probe a g)
    (hn : normSq g = 1) : (1 / 4 : ℝ) ≤ weilQ a g := by
  have hlog : 2 * a < Real.log 2 := by
    have := Real.log_two_gt_d9; norm_num at this; linarith
  rw [weilQ_eq', primeS_eq_zero hlog hp, hn, archE_split ha hp hn]
  have hC := weilConst_ge
  have hF := farField_ge ha ha1
  have hN := nearField_all ha ha1 hp hn
  have hP : 0 ≤ 2 * poleR g a ^ 2 := by positivity
  linarith

end Pilot1ca

#print axioms Pilot1ca.digamma_quarter
#print axioms Pilot1ca.weilConst_eq
#print axioms Pilot1ca.weilConst_ge
#print axioms Pilot1ca.farField_eq
#print axioms Pilot1ca.farField_ge
#print axioms Pilot1ca.nearField_all
#print axioms Pilot1ca.weilQ_ge_quarter
