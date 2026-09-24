import Mathlib
import UniquenessQ

/-! # A certified lower bound on `Q₀` orthogonally to `w`, for every `0 < a ≤ 0.35`

For every support `0 < a ≤ 0.35` (so `δ = 2a ≤ 0.7`, past the first prime `log 2`), every
normalised probe `g` with `ĝ(i/2) = ⟨g, w⟩ = 0` has `Q₀(g) = Q(g) ≥ λ₁ + 1/40`, and `≥ λ₁ + 1/10`
when `2a < log 2`. Hence the ground state of the full form `Q` is unique up to sign there.

The method is an exact Fourier representation, not an approximation.
* **A.** View `g` (supported in `[−a, a]`) on a circle of length `8a`. For `0 ≤ u ≤ 2a` the circular
  and true autocorrelations agree, so `1 − f(u) = Σ_n p_n (1 − cos(πnu/4a))` with `Σ p_n = 1`.
* **B.** Hence the near-field energy is `∫_{(0,2a]}(1 − f)K ≥ τ + Σ_{|n|≤5}(ψ_n − τ)p_n` whenever
  every mode energy `ψ_n = ∫_{(0,2a]}(1 − cos(πnu/4a))K` with `|n| ≥ 6` is at least `τ`.
* **C.** `K(u) = ½csch(u/2) + ½sech(u/2) ≥ 1/u + ½ − r(u)` (Taylor bounds for `exp`), so
  `ψ_n ≥ Cin(πn/2) + a(1 − 2 sin(πn/2)/(πn)) − err(a)`.
* **D.** `Cin(x) = ∫₀ˣ(1 − cos s)/s` is bounded below at `x = πk/2`, `k ≤ 61`, by a Taylor piece and
  tangent-line pieces `1/s ≥ 2/c − s/c²` with exact antiderivatives; from `3π` on the pieces are in
  closed form (`piece_eq`) and the rational sums are checked by kernel evaluation.
* **E.** For even `g` the mode masses are `p_n = (∫ g cos(πnt/4a))²/(8a)`; Cauchy–Schwarz against
  `cos − β_n`, with `(∫ g)² ≤ a⁵/30` from `g ⊥ w`, bounds `p_1, …, p_5`.
* **F–G.** The box has near-field energy `≤ 1 + a/2` and pole term `≤ 4a(1 + a²/24 + a⁴/1600)²`.
* **H–J.** Past `log 2`, the prime `n = 2` enters as `−√2 log 2 · f(log 2)`, and
  `f(log 2) = Σ p_n (cos(ω_n log 2) − cos(ω_n 2a))` since `f(2a) = 0`; each defect is
  `≤ min(ω_n(2a − log 2), 2)`, absorbed mode by mode with tail levels at `n = 6, 11, 21, 61`.

No semiclassical input: only the explicit formula's archimedean kernel, Parseval on a circle, and
elementary calculus. Every number is proved in Lean (the only external constants are Mathlib's
bounds on `π`, `log 2` and `e`).
-/

open Real Filter Topology Complex MeasureTheory Set

noncomputable section

namespace Pilot1ca

/-! ## The kernel, the prime term below `log 2`, the far field -/

theorem kerK_le {u : ℝ} (hu : 0 < u) : kerK u ≤ Real.exp (u / 2) / u := by
  unfold kerK
  exact div_le_div_of_nonneg_left (Real.exp_pos _).le hu (Real.self_le_sinh_iff.2 hu.le)

/-- Below the first prime power (`2a < log 2`) the prime term of every probe vanishes. -/
theorem primeS_eq_zero {a : ℝ} (ha : 2 * a < Real.log 2) {g : ℝ → ℝ} (hg : Probe a g) :
    primeS g = 0 := by
  unfold primeS
  refine (tsum_congr fun n => ?_).trans tsum_zero
  rcases lt_or_ge n 2 with hn | hn
  · interval_cases n <;> simp
  · have hl : Real.log 2 ≤ Real.log n :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hn)
    have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hpos : 0 < Real.log n := by linarith
    have hz : autocorr g (Real.log n) = 0 :=
      autocorr_eq_zero hg.supp (by rw [abs_of_pos hpos]; linarith)
    simp [hz]

theorem box_sq {a : ℝ} (ha : 0 < a) : (1 / Real.sqrt (2 * a)) ^ 2 = 1 / (2 * a) := by
  rw [div_pow, Real.sq_sqrt (by linarith), one_pow]

theorem archIntegrand_eq_kerK {a : ℝ} (ha : 0 ≤ a) {g : ℝ → ℝ} (hg : Probe a g) (hn : normSq g = 1) {u : ℝ}
    (hu : 2 * a < u) : archIntegrand g u = kerK u := by
  unfold archIntegrand kerK
  rw [autocorr_zero, hn, autocorr_eq_zero hg.supp (by rwa [abs_of_pos (by linarith)])]
  ring

/-- `archE g = ∫_{(0,2a]} A_g + ∫_{u > 2a} K` for a normalised probe. -/
theorem archE_split {a : ℝ} (ha : 0 < a) {g : ℝ → ℝ} (hp : Probe a g) (hn : normSq g = 1) :
    archE g = (∫ u in Ioc 0 (2 * a), archIntegrand g u) + ∫ u in Ioi (2 * a), kerK u := by
  unfold archE
  rw [← Ioc_union_Ioi_eq_Ioi (by linarith : (0 : ℝ) ≤ 2 * a),
    setIntegral_union (Ioc_disjoint_Ioi (le_refl _)) measurableSet_Ioi
      (hp.arch.mono_set Ioc_subset_Ioi_self) (hp.arch.mono_set (Ioi_subset_Ioi (by linarith)))]
  congr 1
  exact setIntegral_congr_fun measurableSet_Ioi fun u hu =>
    archIntegrand_eq_kerK ha.le hp hn hu

/-! ## A. The exact Fourier representation on a circle of length `8a` -/

/-- The mode masses `p_n = 8a·|c_n|²` on the circle of length `8a`. -/
def pm (a : ℝ) (g : ℝ → ℝ) (n : ℤ) : ℝ := 8 * a * ‖cf (2 * a) g n‖ ^ 2

theorem pm_nonneg {a : ℝ} (ha : 0 < a) (g : ℝ → ℝ) (n : ℤ) : 0 ≤ pm a g n := by
  unfold pm; positivity

/-- `Σ p_n = ‖g‖²`. -/
theorem hasSum_pm {a : ℝ} (ha : 0 < a) {g : ℝ → ℝ} (hp : Probe a g) :
    HasSum (pm a g) (normSq g) := by
  have h := (hasSum_cf_sq (a := 2 * a) (r := a) (by linarith) (by linarith) hp.memL2 hp.supp).mul_left
    (8 * a)
  have e : 8 * a * ((4 * (2 * a))⁻¹ * normSq g) = normSq g := by field_simp; ring
  rw [e] at h; exact h

/-- **`1 − f(u) = Σ p_n (1 − cos(πnu/4a))`** for `0 ≤ u ≤ 2a`, `‖g‖ = 1`. -/
theorem hasSum_one_sub_autocorr {a : ℝ} (ha : 0 < a) {g : ℝ → ℝ} (hp : Probe a g)
    (hn : normSq g = 1) {u : ℝ} (hu0 : 0 ≤ u) (hu : u ≤ 2 * a) :
    HasSum (fun n : ℤ => pm a g n * (1 - Real.cos (π * n * u / (4 * a)))) (1 - autocorr g u) := by
  have h := (hasSum_shift' (A := 2 * a) (r := a) (by linarith) hp.memL2 hp.supp
    (s := u) (by rw [abs_of_nonneg hu0]; linarith)).mul_left (4 * a)
  rw [autocorr_zero, hn] at h
  convert h using 1
  · funext n
    unfold pm
    rw [show 2 * π * (n : ℝ) * u / (4 * (2 * a)) = π * n * u / (4 * a) by field_simp]
    ring
  · field_simp


/-! ## B. The energy as a sum over modes -/

/-- The mode energy `ψ_n = ∫_{(0,2a]} (1 − cos(πnu/4a)) K(u) du`. -/
def modeE (a : ℝ) (n : ℤ) : ℝ := ∫ u in Ioc 0 (2 * a), (1 - Real.cos (π * n * u / (4 * a))) * kerK u

theorem modeE_integrable {a : ℝ} (ha : 0 < a) (n : ℤ) :
    IntegrableOn (fun u => (1 - Real.cos (π * n * u / (4 * a))) * kerK u) (Ioc 0 (2 * a)) := by
  set ω := π * n / (4 * a)
  have hm : Measurable (fun u => (1 - Real.cos (π * n * u / (4 * a))) * kerK u) :=
    (measurable_const.sub (Real.continuous_cos.measurable.comp (by fun_prop))).mul kerK_measurable
  refine (integrableOn_const (C := ω ^ 2 * a * Real.exp a) measure_Ioc_lt_top.ne).mono'
    hm.aestronglyMeasurable ((ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall
      fun u hu => ?_))
  have hu0 := hu.1
  have hK0 : 0 ≤ kerK u := (kerK_pos hu0).le
  have hc1 : 0 ≤ 1 - Real.cos (π * n * u / (4 * a)) := by linarith [Real.cos_le_one (π * n * u / (4 * a))]
  have hc2 : 1 - Real.cos (π * n * u / (4 * a)) ≤ (ω * u) ^ 2 / 2 := by
    have := Real.one_sub_sq_div_two_le_cos (x := π * n * u / (4 * a))
    have e : π * n * u / (4 * a) = ω * u := by simp only [ω]; ring
    rw [e] at this ⊢; linarith
  have hK := kerK_le hu0
  have he : Real.exp (u / 2) ≤ Real.exp a := Real.exp_le_exp.2 (by linarith [hu.2])
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hc1 hK0)]
  calc (1 - Real.cos (π * n * u / (4 * a))) * kerK u ≤ (ω * u) ^ 2 / 2 * (Real.exp (u / 2) / u) :=
        mul_le_mul hc2 hK hK0 (by positivity)
    _ = ω ^ 2 * (u / 2) * Real.exp (u / 2) := by field_simp
    _ ≤ ω ^ 2 * a * Real.exp a := by
        have : u / 2 ≤ a := by linarith [hu.2]
        have := sq_nonneg ω
        gcongr

theorem modeE_neg (a : ℝ) (n : ℤ) : modeE a (-n) = modeE a n := by
  unfold modeE; congr 1; funext u; push_cast
  rw [show π * -(n : ℝ) * u / (4 * a) = -(π * n * u / (4 * a)) by ring, Real.cos_neg]

/-- **Finite partial sums of the mode expansion are below the near-field energy.** -/
theorem sum_modeE_le {a : ℝ} (ha : 0 < a) {g : ℝ → ℝ} (hp : Probe a g) (hn : normSq g = 1)
    (S : Finset ℤ) :
    ∑ n ∈ S, pm a g n * modeE a n ≤ ∫ u in Ioc 0 (2 * a), archIntegrand g u := by
  have e : ∑ n ∈ S, pm a g n * modeE a n
      = ∫ u in Ioc 0 (2 * a), ∑ n ∈ S, pm a g n * ((1 - Real.cos (π * n * u / (4 * a))) * kerK u) := by
    rw [integral_finsetSum S fun n _ => (modeE_integrable ha n).const_mul _]
    refine Finset.sum_congr rfl fun n _ => ?_
    unfold modeE; rw [integral_const_mul]
  rw [e]
  refine setIntegral_mono_on (integrable_finsetSum S fun n _ => (modeE_integrable ha n).const_mul _)
    (hp.arch.mono_set Ioc_subset_Ioi_self) measurableSet_Ioc fun u hu => ?_
  have hK0 : 0 ≤ kerK u := (kerK_pos hu.1).le
  have hs := sum_le_hasSum S (fun n _ => mul_nonneg (pm_nonneg ha g n)
    (by linarith [Real.cos_le_one (π * n * u / (4 * a))]))
    (hasSum_one_sub_autocorr ha hp hn hu.1.le hu.2)
  have e2 : archIntegrand g u = (1 - autocorr g u) * kerK u := by
    unfold archIntegrand kerK; rw [autocorr_zero, hn]
  rw [e2]
  calc ∑ n ∈ S, pm a g n * ((1 - Real.cos (π * n * u / (4 * a))) * kerK u)
      = (∑ n ∈ S, pm a g n * (1 - Real.cos (π * n * u / (4 * a)))) * kerK u := by
        rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun n _ => by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hs hK0

/-- **The truncated lower bound**: if every mode outside `S₀` has energy at least `τ ≥ 0`, then
`τ + Σ_{S₀} (ψ_n − τ) p_n ≤ ∫_{(0,2a]} A_g`. -/
theorem energy_ge_trunc {a : ℝ} (ha : 0 < a) {g : ℝ → ℝ} (hp : Probe a g) (hn : normSq g = 1)
    (S₀ : Finset ℤ) {τ : ℝ} (hτ : ∀ n, n ∉ S₀ → τ ≤ modeE a n) :
    τ + ∑ n ∈ S₀, (modeE a n - τ) * pm a g n ≤ ∫ u in Ioc 0 (2 * a), archIntegrand g u := by
  have hP := hasSum_pm ha hp
  rw [hn] at hP
  have hT : Tendsto (fun S : Finset ℤ => ∑ n ∈ S₀, (modeE a n - τ) * pm a g n
      + τ * ∑ n ∈ S, pm a g n) atTop (𝓝 (∑ n ∈ S₀, (modeE a n - τ) * pm a g n + τ * 1)) :=
    tendsto_const_nhds.add (hP.const_mul τ)
  rw [mul_one, add_comm] at hT
  refine le_of_tendsto hT ?_
  filter_upwards [eventually_ge_atTop S₀] with S hS
  have hsplit := Finset.sum_sdiff hS (f := pm a g)
  have hsplit2 := Finset.sum_sdiff hS (f := fun n => pm a g n * modeE a n)
  have htail : τ * ∑ n ∈ S \ S₀, pm a g n ≤ ∑ n ∈ S \ S₀, pm a g n * modeE a n := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun n hn' => ?_
    rw [Finset.mem_sdiff] at hn'
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left (hτ n hn'.2) (pm_nonneg ha g n)
  have hlow : ∑ n ∈ S₀, (modeE a n - τ) * pm a g n
      = ∑ n ∈ S₀, pm a g n * modeE a n - τ * ∑ n ∈ S₀, pm a g n := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun n _ => by ring
  have hle := sum_modeE_le ha hp hn S
  rw [← hsplit, mul_add] at *
  rw [← hsplit2] at hle
  linarith

/-! ## C. The kernel sandwich and the mode energies -/

theorem kerK_eq {u : ℝ} (hu : 0 < u) :
    kerK u = 1 / 2 / Real.sinh (u / 2) + 1 / 2 / Real.cosh (u / 2) := by
  unfold kerK
  have hs : 0 < Real.sinh (u / 2) := Real.sinh_pos_iff.2 (by linarith)
  have hc : 0 < Real.cosh (u / 2) := Real.cosh_pos _
  have e1 : Real.sinh u = 2 * Real.sinh (u / 2) * Real.cosh (u / 2) := by
    rw [← Real.sinh_two_mul]; ring_nf
  have e2 : Real.exp (u / 2) = Real.cosh (u / 2) + Real.sinh (u / 2) := (Real.cosh_add_sinh _).symm
  rw [e1, e2]; field_simp

/-- `K(u) ≤ 1/u + 1/2`. -/
theorem kerK_le' {u : ℝ} (hu : 0 < u) : kerK u ≤ 1 / u + 1 / 2 := by
  rw [kerK_eq hu]
  have hs : u / 2 ≤ Real.sinh (u / 2) := Real.self_le_sinh_iff.2 (by linarith)
  have hc : 1 ≤ Real.cosh (u / 2) := Real.one_le_cosh _
  have h1 : 1 / 2 / Real.sinh (u / 2) ≤ 1 / u := by
    rw [div_div, div_le_div_iff₀ (by positivity) hu]; linarith
  have h2 : 1 / 2 / Real.cosh (u / 2) ≤ 1 / 2 := div_le_self (by norm_num) hc
  linarith

theorem sinh_le_taylor {y : ℝ} (hy0 : 0 ≤ y) (hy : y ≤ 1) :
    Real.sinh y ≤ y + y ^ 3 / 6 + y ^ 5 / 100 := by
  have h1 := Real.exp_bound (x := y) (by rw [abs_of_nonneg hy0]; exact hy) (n := 5) (by norm_num)
  have h2 := Real.exp_bound (x := -y) (by rw [abs_neg, abs_of_nonneg hy0]; exact hy) (n := 5)
    (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.succ_eq_add_one]
    at h1 h2
  rw [abs_neg, abs_of_nonneg hy0] at h2
  rw [abs_of_nonneg hy0] at h1
  rw [Real.sinh_eq]
  have a1 := (abs_le.1 h1).2
  have a2 := (abs_le.1 h2).1
  norm_num at a1 a2 ⊢
  nlinarith [pow_nonneg hy0 5]

theorem cosh_le_taylor {y : ℝ} (hy : |y| ≤ 1) :
    Real.cosh y ≤ 1 + y ^ 2 / 2 + 5 * y ^ 4 / 96 := by
  have h1 := Real.exp_bound (x := y) hy (n := 4) (by norm_num)
  have h2 := Real.exp_bound (x := -y) (by rwa [abs_neg]) (n := 4) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.succ_eq_add_one]
    at h1 h2
  rw [abs_neg] at h2
  rw [Real.cosh_eq]
  have a1 := (abs_le.1 h1).2
  have a2 := (abs_le.1 h2).2
  have hy4 : |y| ^ 4 = y ^ 4 := by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq_abs, ← pow_mul]
  rw [hy4] at a1 a2
  norm_num at a1 a2 ⊢
  nlinarith

/-- The remainder `r(u) = u/24 + u²/16 + u³/1600 + 5u⁴/3072`. -/
def remK (u : ℝ) : ℝ := u / 24 + u ^ 2 / 16 + u ^ 3 / 1600 + 5 * u ^ 4 / 3072

/-- `K(u) ≥ 1/u + 1/2 − r(u)` on `(0, 2]`. -/
theorem kerK_ge_taylor {u : ℝ} (hu : 0 < u) (hu2 : u ≤ 2) : 1 / u + 1 / 2 - remK u ≤ kerK u := by
  rw [kerK_eq hu]
  set y := u / 2 with hy
  have hy0 : 0 < y := by linarith
  have hy1 : y ≤ 1 := by linarith
  have hs := sinh_le_taylor hy0.le hy1
  have hc := cosh_le_taylor (y := y) (by rw [abs_of_pos hy0]; exact hy1)
  have hsp : 0 < Real.sinh y := Real.sinh_pos_iff.2 hy0
  have hcp : 0 < Real.cosh y := Real.cosh_pos _
  -- `1/sinh y ≥ (1/y)(1 − y²/6 − y⁴/100)`, `1/cosh y ≥ 2 − cosh y`
  have i1 : (1 - y ^ 2 / 6 - y ^ 4 / 100) / y ≤ 1 / Real.sinh y := by
    rw [div_le_div_iff₀ hy0 hsp, one_mul]
    have : Real.sinh y * (1 - y ^ 2 / 6 - y ^ 4 / 100)
        ≤ (y + y ^ 3 / 6 + y ^ 5 / 100) * (1 - y ^ 2 / 6 - y ^ 4 / 100) := by
      apply mul_le_mul_of_nonneg_right hs; nlinarith [pow_le_one₀ hy0.le hy1 (n := 2),
        pow_le_one₀ hy0.le hy1 (n := 4)]
    nlinarith [pow_pos hy0 3, pow_pos hy0 5, pow_pos hy0 7, pow_pos hy0 9]
  have i2 : 2 - Real.cosh y ≤ 1 / Real.cosh y := by
    rw [le_div_iff₀ hcp]; nlinarith [sq_nonneg (Real.cosh y - 1)]
  unfold remK
  have e1 : 1 / 2 / Real.sinh y = (1 / 2) * (1 / Real.sinh y) := by ring
  have e2 : 1 / 2 / Real.cosh y = (1 / 2) * (1 / Real.cosh y) := by ring
  rw [e1, e2]
  have e3 : (1 - y ^ 2 / 6 - y ^ 4 / 100) / y = 2 / u - u / 12 - u ^ 3 / 800 := by
    rw [hy]; field_simp; ring
  rw [e3] at i1
  have e4 : 1 / u = (1 / 2) * (2 / u) := by ring
  rw [e4]
  have hy2 : y ^ 2 = u ^ 2 / 4 := by rw [hy]; ring
  have hy4 : y ^ 4 = u ^ 4 / 16 := by rw [hy]; ring
  rw [hy2, hy4] at hc
  linarith

/-- `Cin(x) = ∫₀ˣ (1 − cos s)/s ds`. -/
def Cin (x : ℝ) : ℝ := ∫ s in (0 : ℝ)..x, (1 - Real.cos s) / s

theorem Cin_integrable (b : ℝ) : IntegrableOn (fun s => (1 - Real.cos s) / s) (Ioc 0 b) := by
  have := (integrableOn_weight b 1).div_const 2
  refine IntegrableOn.congr_fun this (fun s _ => ?_) measurableSet_Ioc
  simp only [one_mul]; ring

theorem Cin_ii {b : ℝ} (hb : 0 ≤ b) :
    IntervalIntegrable (fun s => (1 - Real.cos s) / s) volume 0 b :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le hb).2 (Cin_integrable b)

theorem Cin_integrand_nonneg {s : ℝ} (hs : 0 ≤ s) : 0 ≤ (1 - Real.cos s) / s :=
  div_nonneg (by linarith [Real.cos_le_one s]) hs

theorem Cin_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) : Cin x ≤ Cin y := by
  unfold Cin
  have hxy_ii : IntervalIntegrable (fun s => (1 - Real.cos s) / s) volume x y :=
    (Cin_ii (hx.trans hxy)).mono_set (by
      rw [uIcc_of_le hxy, uIcc_of_le (hx.trans hxy)]; exact Icc_subset_Icc hx le_rfl)
  rw [← intervalIntegral.integral_add_adjacent_intervals (Cin_ii hx) hxy_ii]
  have := intervalIntegral.integral_nonneg (μ := volume) hxy (fun s hs => Cin_integrand_nonneg (hx.trans hs.1))
  linarith

/-- The error term `err(a) = 2∫₀^{2a} r`. -/
def errK (a : ℝ) : ℝ := a ^ 2 / 6 + a ^ 3 / 3 + a ^ 4 / 200 + a ^ 5 / 48

/-- **Mode energy lower bound**: `ψ_n ≥ Cin(πn/2) + a(1 − 2 sin(πn/2)/(πn)) − err(a)`. -/
theorem modeE_ge {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) {n : ℤ} (hn : 0 < n) :
    Cin (π * n / 2) + a * (1 - 2 * Real.sin (π * n / 2) / (π * n)) - errK a ≤ modeE a n := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  set ω := π * n / (4 * a) with hω
  have hω0 : 0 < ω := by positivity
  have e0 : ∀ u, π * n * u / (4 * a) = ω * u := fun u => by rw [hω]; ring
  set F : ℝ → ℝ := fun u => (1 - Real.cos (ω * u)) / u + (1 - Real.cos (ω * u)) / 2 - 2 * remK u
    with hF
  have hFi1 : IntegrableOn (fun u => (1 - Real.cos (ω * u)) / u) (Ioc 0 (2 * a)) := by
    have := (integrableOn_weight (2 * a) ω).div_const 2
    refine IntegrableOn.congr_fun this (fun s _ => ?_) measurableSet_Ioc
    ring
  have hc : Continuous (fun u => (1 - Real.cos (ω * u)) / 2 - 2 * remK u) := by
    unfold remK; fun_prop
  have hFi : IntegrableOn F (Ioc 0 (2 * a)) := by
    have := hFi1.add (hc.integrableOn_Ioc (a := 0) (b := 2 * a))
    refine IntegrableOn.congr_fun this (fun s _ => ?_) measurableSet_Ioc
    simp only [hF, Pi.add_apply]; ring
  have hpt : ∀ u ∈ Ioc 0 (2 * a), F u ≤ (1 - Real.cos (π * n * u / (4 * a))) * kerK u := by
    intro u hu
    rw [e0]
    have hK := kerK_ge_taylor hu.1 (by linarith [hu.2])
    have hr : 0 ≤ remK u := by unfold remK; have := hu.1; positivity
    have c1 : 0 ≤ 1 - Real.cos (ω * u) := by linarith [Real.cos_le_one (ω * u)]
    have c2 : 1 - Real.cos (ω * u) ≤ 2 := by linarith [Real.neg_one_le_cos (ω * u)]
    have e1 : (1 - Real.cos (ω * u)) / u = (1 - Real.cos (ω * u)) * (1 / u) := by ring
    simp only [hF]; rw [e1]
    nlinarith [mul_le_mul_of_nonneg_left hK c1, mul_le_mul_of_nonneg_right c2 hr]
  have hmono := setIntegral_mono_on hFi (modeE_integrable ha n) measurableSet_Ioc hpt
  -- evaluate `∫ F`
  have h2a : (0 : ℝ) ≤ 2 * a := by linarith
  rw [← intervalIntegral.integral_of_le h2a] at hmono
  have iA : IntervalIntegrable (fun u => (1 - Real.cos (ω * u)) / u) volume 0 (2 * a) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le h2a).2 hFi1
  have iB : IntervalIntegrable (fun u => (1 - Real.cos (ω * u)) / 2) volume 0 (2 * a) :=
    (by fun_prop : Continuous (fun u => (1 - Real.cos (ω * u)) / 2)).intervalIntegrable _ _
  have iC : IntervalIntegrable (fun u => 2 * remK u) volume 0 (2 * a) :=
    (by unfold remK; fun_prop : Continuous (fun u => 2 * remK u)).intervalIntegrable _ _
  have hI : (∫ u in (0 : ℝ)..(2 * a), F u) = (∫ u in (0 : ℝ)..(2 * a), (1 - Real.cos (ω * u)) / u)
      + (∫ u in (0 : ℝ)..(2 * a), (1 - Real.cos (ω * u)) / 2)
      - ∫ u in (0 : ℝ)..(2 * a), 2 * remK u := by
    simp only [hF]
    rw [intervalIntegral.integral_sub (iA.add iB) iC, intervalIntegral.integral_add iA iB]
  -- the three integrals
  have hI1 : (∫ u in (0 : ℝ)..(2 * a), (1 - Real.cos (ω * u)) / u) = Cin (π * n / 2) := by
    have h := intervalIntegral.integral_comp_mul_left (a := 0) (b := 2 * a)
      (fun s => (1 - Real.cos s) / s) hω0.ne'
    have e : (fun u => (1 - Real.cos (ω * u)) / u) = fun u => ω * ((1 - Real.cos (ω * u)) / (ω * u)) := by
      funext u
      by_cases hu : u = 0
      · simp [hu]
      · field_simp
    rw [e, intervalIntegral.integral_const_mul, h, smul_eq_mul, mul_zero,
      show ω * (2 * a) = π * n / 2 by rw [hω]; field_simp; ring]
    unfold Cin; field_simp
  have hI2 : (∫ u in (0 : ℝ)..(2 * a), (1 - Real.cos (ω * u)) / 2)
      = a * (1 - 2 * Real.sin (π * n / 2) / (π * n)) := by
    have hcos : (∫ u in (0 : ℝ)..(2 * a), Real.cos (ω * u)) = Real.sin (π * n / 2) / ω := by
      rw [intervalIntegral.integral_comp_mul_left (fun s => Real.cos s) hω0.ne', integral_cos,
        mul_zero, Real.sin_zero, sub_zero, smul_eq_mul,
        show ω * (2 * a) = π * n / 2 by rw [hω]; field_simp; ring]
      field_simp
    rw [intervalIntegral.integral_div, intervalIntegral.integral_sub intervalIntegrable_const
      ((by fun_prop : Continuous (fun u => Real.cos (ω * u))).intervalIntegrable _ _), hcos,
      intervalIntegral.integral_const, smul_eq_mul, mul_one, sub_zero, hω]
    field_simp; ring
  have hI3 : (∫ u in (0 : ℝ)..(2 * a), 2 * remK u) = errK a := by
    unfold remK errK
    simp only [intervalIntegral.integral_const_mul]
    rw [intervalIntegral.integral_add, intervalIntegral.integral_add, intervalIntegral.integral_add]
    · simp only [intervalIntegral.integral_div, intervalIntegral.integral_const_mul, integral_pow,
        integral_id]
      ring
    all_goals exact (by fun_prop : Continuous _).intervalIntegrable _ _
  rw [hI, hI1, hI2, hI3] at hmono
  exact hmono

/-! ## D. Certified values of `Cin(πk/2)` -/

/-- An antiderivative of `(1 − cos s)(2/c − s/c²)`. -/
def Fk (c s : ℝ) : ℝ := 2 / c * (s - Real.sin s) - 1 / c ^ 2 * (s ^ 2 / 2 - Real.cos s - s * Real.sin s)

theorem Fk_deriv (c s : ℝ) :
    HasDerivAt (Fk c) ((1 - Real.cos s) * (2 / c - s / c ^ 2)) s := by
  have h1 : HasDerivAt (fun s => s - Real.sin s) (1 - Real.cos s) s :=
    (hasDerivAt_id s).sub (Real.hasDerivAt_sin s)
  have h2 : HasDerivAt (fun s => s ^ 2 / 2 - Real.cos s - s * Real.sin s)
      (s * (1 - Real.cos s)) s := by
    have := (((hasDerivAt_pow 2 s).div_const 2).sub (Real.hasDerivAt_cos s)).sub
      ((hasDerivAt_id s).mul (Real.hasDerivAt_sin s))
    exact this.congr_deriv (by simp; ring)
  have := (h1.const_mul (2 / c)).sub (h2.const_mul (1 / c ^ 2))
  exact this.congr_deriv (by ring)

/-- **One tangent-line step**: `Cin(β) ≥ Cin(α) + F_c(β) − F_c(α)`, from `1/s ≥ 2/c − s/c²`. -/
theorem cin_step {α β c : ℝ} (hα : 0 < α) (hαβ : α ≤ β) (hc : 0 < c) :
    Cin α + (Fk c β - Fk c α) ≤ Cin β := by
  unfold Cin
  have hii : IntervalIntegrable (fun s => (1 - Real.cos s) / s) volume α β :=
    (Cin_ii (hα.le.trans hαβ)).mono_set (by
      rw [uIcc_of_le hαβ, uIcc_of_le (hα.le.trans hαβ)]; exact Icc_subset_Icc hα.le le_rfl)
  rw [← intervalIntegral.integral_add_adjacent_intervals (Cin_ii hα.le) hii]
  have hcont : Continuous (fun s => (1 - Real.cos s) * (2 / c - s / c ^ 2)) := by fun_prop
  have hF : (∫ s in α..β, (1 - Real.cos s) * (2 / c - s / c ^ 2)) = Fk c β - Fk c α :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => Fk_deriv c s)
      (hcont.intervalIntegrable _ _)
  have hmono := intervalIntegral.integral_mono_on hαβ (hcont.intervalIntegrable _ _) hii
    (fun s hs => by
      have hs0 : 0 < s := hα.trans_le hs.1
      have h1 : 0 ≤ 1 - Real.cos s := by linarith [Real.cos_le_one s]
      have h2 : 2 / c - s / c ^ 2 ≤ 1 / s := by
        rw [div_sub_div _ _ hc.ne' (by positivity), div_le_div_iff₀ (by positivity) hs0]
        nlinarith [sq_nonneg (s - c), hc]
      calc (1 - Real.cos s) * (2 / c - s / c ^ 2) ≤ (1 - Real.cos s) * (1 / s) :=
            mul_le_mul_of_nonneg_left h2 h1
        _ = (1 - Real.cos s) / s := by ring)
  rw [hF] at hmono
  linarith

theorem cin_quarter : (0.14925 : ℝ) ≤ Cin (1 * π / 4) := by
  have hπ1 := Real.pi_gt_d6
  have hπ2 := Real.pi_lt_d6
  rw [one_mul]
  unfold Cin
  have h0 : (0 : ℝ) ≤ π / 4 := by positivity
  have hmono := intervalIntegral.integral_mono_on h0
    ((by fun_prop : Continuous (fun s : ℝ => s / 2 - 5 * s ^ 3 / 96)).intervalIntegrable _ _)
    (Cin_ii h0) (fun s hs => by
      rcases hs.1.eq_or_lt with h | hs0
      · rw [← h]; simp
      · have hs1 : |s| ≤ 1 := by rw [abs_of_pos hs0]; linarith [hs.2]
        have hb := (abs_le.1 (Real.cos_bound hs1)).2
        rw [abs_of_pos hs0] at hb
        rw [le_div_iff₀ hs0]
        nlinarith)
  have hval : (∫ s in (0 : ℝ)..(π / 4), (s / 2 - 5 * s ^ 3 / 96))
      = (π / 4) ^ 2 / 4 - 5 * (π / 4) ^ 4 / 384 := by
    rw [intervalIntegral.integral_sub, intervalIntegral.integral_div, intervalIntegral.integral_div,
      intervalIntegral.integral_const_mul, integral_id, integral_pow]
    · ring
    · exact (by fun_prop : Continuous (fun s : ℝ => s / 2)).intervalIntegrable _ _
    · exact (by fun_prop : Continuous (fun s : ℝ => 5 * s ^ 3 / 96)).intervalIntegrable _ _
  rw [hval] at hmono
  nlinarith [sq_nonneg π, pow_pos Real.pi_pos 3, pow_pos Real.pi_pos 4]

theorem num_atoms :
    (0.3183097 : ℝ) < 1 / π ∧ 1 / π < (0.31831 : ℝ) ∧
    (1.414213 : ℝ) < Real.sqrt 2 ∧ Real.sqrt 2 < (1.414214 : ℝ) ∧
    (0.3183097 * 1.414213 : ℝ) < 1 / π * Real.sqrt 2 ∧ 1 / π * Real.sqrt 2 < (0.31831 * 1.414214 : ℝ) ∧
    (0.3183097 ^ 2 : ℝ) < (1 / π) ^ 2 ∧ (1 / π) ^ 2 < (0.31831 ^ 2 : ℝ) ∧
    (0.3183097 ^ 2 * 1.414213 : ℝ) < (1 / π) ^ 2 * Real.sqrt 2 ∧
    (1 / π) ^ 2 * Real.sqrt 2 < (0.31831 ^ 2 * 1.414214 : ℝ) := by
  have hπ1 := Real.pi_gt_d6
  have hπ2 := Real.pi_lt_d6
  have hx1 : (0.3183097 : ℝ) < 1 / π := by rw [lt_div_iff₀ Real.pi_pos]; nlinarith
  have hx2 : 1 / π < (0.31831 : ℝ) := by rw [div_lt_iff₀ Real.pi_pos]; nlinarith
  have hs1 : (1.414213 : ℝ) < Real.sqrt 2 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have hs2 : Real.sqrt 2 < (1.414214 : ℝ) := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hx0 : (0 : ℝ) < 1 / π := by positivity
  refine ⟨hx1, hx2, hs1, hs2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact mul_lt_mul'' hx1 hs1 (by norm_num) (by norm_num)
  · exact mul_lt_mul'' hx2 hs2 hx0.le (by positivity)
  · exact pow_lt_pow_left₀ hx1 (by norm_num) (by norm_num)
  · exact pow_lt_pow_left₀ hx2 hx0.le (by norm_num)
  · exact mul_lt_mul'' (pow_lt_pow_left₀ hx1 (by norm_num) (by norm_num)) hs1 (by norm_num) (by norm_num)
  · exact mul_lt_mul'' (pow_lt_pow_left₀ hx2 hx0.le (by norm_num)) hs2 (by positivity) (by positivity)

theorem sc0 : Real.sin (0 * π / 4) = 0 ∧ Real.cos (0 * π / 4) = 1 := by simp

theorem sc1 : Real.sin (1 * π / 4) = Real.sqrt 2 / 2 ∧ Real.cos (1 * π / 4) = Real.sqrt 2 / 2 := by
  rw [one_mul]; exact ⟨Real.sin_pi_div_four, Real.cos_pi_div_four⟩

theorem sc2 : Real.sin (2 * π / 4) = 1 ∧ Real.cos (2 * π / 4) = 0 := by
  obtain ⟨h1, h2⟩ := sc0
  rw [show (2 : ℝ) * π / 4 = 0 * π / 4 + π / 2 by ring, Real.sin_add_pi_div_two,
    Real.cos_add_pi_div_two, h1, h2]
  constructor <;> ring

theorem sc3 : Real.sin (3 * π / 4) = Real.sqrt 2/2 ∧ Real.cos (3 * π / 4) = -Real.sqrt 2/2 := by
  obtain ⟨h1, h2⟩ := sc1
  rw [show (3 : ℝ) * π / 4 = 1 * π / 4 + π / 2 by ring, Real.sin_add_pi_div_two,
    Real.cos_add_pi_div_two, h1, h2]
  constructor <;> ring

theorem sc4 : Real.sin (4 * π / 4) = 0 ∧ Real.cos (4 * π / 4) = -1 := by
  obtain ⟨h1, h2⟩ := sc2
  rw [show (4 : ℝ) * π / 4 = 2 * π / 4 + π / 2 by ring, Real.sin_add_pi_div_two,
    Real.cos_add_pi_div_two, h1, h2]
  constructor <;> ring

theorem sc5 : Real.sin (5 * π / 4) = -Real.sqrt 2/2 ∧ Real.cos (5 * π / 4) = -Real.sqrt 2/2 := by
  obtain ⟨h1, h2⟩ := sc3
  rw [show (5 : ℝ) * π / 4 = 3 * π / 4 + π / 2 by ring, Real.sin_add_pi_div_two,
    Real.cos_add_pi_div_two, h1, h2]
  constructor <;> ring

theorem sc6 : Real.sin (6 * π / 4) = -1 ∧ Real.cos (6 * π / 4) = 0 := by
  obtain ⟨h1, h2⟩ := sc4
  rw [show (6 : ℝ) * π / 4 = 4 * π / 4 + π / 2 by ring, Real.sin_add_pi_div_two,
    Real.cos_add_pi_div_two, h1, h2]
  constructor <;> ring

theorem sc7 : Real.sin (7 * π / 4) = -Real.sqrt 2/2 ∧ Real.cos (7 * π / 4) = Real.sqrt 2/2 := by
  obtain ⟨h1, h2⟩ := sc5
  rw [show (7 : ℝ) * π / 4 = 5 * π / 4 + π / 2 by ring, Real.sin_add_pi_div_two,
    Real.cos_add_pi_div_two, h1, h2]
  constructor <;> ring

theorem sc8 : Real.sin (8 * π / 4) = 0 ∧ Real.cos (8 * π / 4) = 1 := by
  obtain ⟨h1, h2⟩ := sc6
  rw [show (8 : ℝ) * π / 4 = 6 * π / 4 + π / 2 by ring, Real.sin_add_pi_div_two,
    Real.cos_add_pi_div_two, h1, h2]
  constructor <;> ring

theorem sc9 : Real.sin (9 * π / 4) = Real.sqrt 2/2 ∧ Real.cos (9 * π / 4) = Real.sqrt 2/2 := by
  obtain ⟨h1, h2⟩ := sc7
  rw [show (9 : ℝ) * π / 4 = 7 * π / 4 + π / 2 by ring, Real.sin_add_pi_div_two,
    Real.cos_add_pi_div_two, h1, h2]
  constructor <;> ring

theorem sc10 : Real.sin (10 * π / 4) = 1 ∧ Real.cos (10 * π / 4) = 0 := by
  obtain ⟨h1, h2⟩ := sc8
  rw [show (10 : ℝ) * π / 4 = 8 * π / 4 + π / 2 by ring, Real.sin_add_pi_div_two,
    Real.cos_add_pi_div_two, h1, h2]
  constructor <;> ring

theorem sc11 : Real.sin (11 * π / 4) = Real.sqrt 2/2 ∧ Real.cos (11 * π / 4) = -Real.sqrt 2/2 := by
  obtain ⟨h1, h2⟩ := sc9
  rw [show (11 : ℝ) * π / 4 = 9 * π / 4 + π / 2 by ring, Real.sin_add_pi_div_two,
    Real.cos_add_pi_div_two, h1, h2]
  constructor <;> ring

theorem sc12 : Real.sin (12 * π / 4) = 0 ∧ Real.cos (12 * π / 4) = -1 := by
  obtain ⟨h1, h2⟩ := sc10
  rw [show (12 : ℝ) * π / 4 = 10 * π / 4 + π / 2 by ring, Real.sin_add_pi_div_two,
    Real.cos_add_pi_div_two, h1, h2]
  constructor <;> ring

theorem piece1 : (0.391586 : ℝ) ≤ Fk (3 * π / 8) (2 * π / 4) - Fk (3 * π / 8) (1 * π / 4) := by
  obtain ⟨sa, ca⟩ := sc1
  obtain ⟨sb, cb⟩ := sc2
  have key : Fk (3 * π / 8) (2 * π / 4) - Fk (3 * π / 8) (1 * π / 4)
      = 2 / 3 + (1 / π) * (16*Real.sqrt 2/9 - 16/9) + (1 / π) ^ 2 * (-32*Real.sqrt 2/9) := by
    unfold Fk; rw [sa, ca, sb, cb]; field_simp; ring
  rw [key]
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ := num_atoms
  nlinarith

theorem piece2 : (0.53964 : ℝ) ≤ Fk (5 * π / 8) (3 * π / 4) - Fk (5 * π / 8) (2 * π / 4) := by
  obtain ⟨sa, ca⟩ := sc2
  obtain ⟨sb, cb⟩ := sc3
  have key : Fk (5 * π / 8) (3 * π / 4) - Fk (5 * π / 8) (2 * π / 4)
      = 2 / 5 + (1 / π) * (48/25 - 16*Real.sqrt 2/25) + (1 / π) ^ 2 * (-32*Real.sqrt 2/25) := by
    unfold Fk; rw [sa, ca, sb, cb]; field_simp; ring
  rw [key]
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ := num_atoms
  nlinarith

theorem piece3 : (0.540932 : ℝ) ≤ Fk (7 * π / 8) (4 * π / 4) - Fk (7 * π / 8) (3 * π / 4) := by
  obtain ⟨sa, ca⟩ := sc3
  obtain ⟨sb, cb⟩ := sc4
  have key : Fk (7 * π / 8) (4 * π / 4) - Fk (7 * π / 8) (3 * π / 4)
      = 2 / 7 + (1 / π) * (32*Real.sqrt 2/49) + (1 / π) ^ 2 * (32*Real.sqrt 2/49 - 64/49) := by
    unfold Fk; rw [sa, ca, sb, cb]; field_simp; ring
  rw [key]
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ := num_atoms
  nlinarith

theorem piece4 : (0.423508 : ℝ) ≤ Fk (9 * π / 8) (5 * π / 4) - Fk (9 * π / 8) (4 * π / 4) := by
  obtain ⟨sa, ca⟩ := sc4
  obtain ⟨sb, cb⟩ := sc5
  have key : Fk (9 * π / 8) (5 * π / 4) - Fk (9 * π / 8) (4 * π / 4)
      = 2 / 9 + (1 / π) * (32*Real.sqrt 2/81) + (1 / π) ^ 2 * (64/81 - 32*Real.sqrt 2/81) := by
    unfold Fk; rw [sa, ca, sb, cb]; field_simp; ring
  rw [key]
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ := num_atoms
  nlinarith

theorem piece5 : (0.251588 : ℝ) ≤ Fk (11 * π / 8) (6 * π / 4) - Fk (11 * π / 8) (5 * π / 4) := by
  obtain ⟨sa, ca⟩ := sc5
  obtain ⟨sb, cb⟩ := sc6
  have key : Fk (11 * π / 8) (6 * π / 4) - Fk (11 * π / 8) (5 * π / 4)
      = 2 / 11 + (1 / π) * (80/121 - 48*Real.sqrt 2/121) + (1 / π) ^ 2 * (32*Real.sqrt 2/121) := by
    unfold Fk; rw [sa, ca, sb, cb]; field_simp; ring
  rw [key]
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ := num_atoms
  nlinarith

theorem piece6 : (0.09788 : ℝ) ≤ Fk (13 * π / 8) (7 * π / 4) - Fk (13 * π / 8) (6 * π / 4) := by
  obtain ⟨sa, ca⟩ := sc6
  obtain ⟨sb, cb⟩ := sc7
  have key : Fk (13 * π / 8) (7 * π / 4) - Fk (13 * π / 8) (6 * π / 4)
      = 2 / 13 + (1 / π) * (48*Real.sqrt 2/169 - 112/169) + (1 / π) ^ 2 * (32*Real.sqrt 2/169) := by
    unfold Fk; rw [sa, ca, sb, cb]; field_simp; ring
  rw [key]
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ := num_atoms
  nlinarith

theorem piece7 : (0.013727 : ℝ) ≤ Fk (15 * π / 8) (8 * π / 4) - Fk (15 * π / 8) (7 * π / 4) := by
  obtain ⟨sa, ca⟩ := sc7
  obtain ⟨sb, cb⟩ := sc8
  have key : Fk (15 * π / 8) (8 * π / 4) - Fk (15 * π / 8) (7 * π / 4)
      = 2 / 15 + (1 / π) * (-64*Real.sqrt 2/225) + (1 / π) ^ 2 * (64/225 - 32*Real.sqrt 2/225) := by
    unfold Fk; rw [sa, ca, sb, cb]; field_simp; ring
  rw [key]
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ := num_atoms
  nlinarith

theorem piece8 : (0.011384 : ℝ) ≤ Fk (17 * π / 8) (9 * π / 4) - Fk (17 * π / 8) (8 * π / 4) := by
  obtain ⟨sa, ca⟩ := sc8
  obtain ⟨sb, cb⟩ := sc9
  have key : Fk (17 * π / 8) (9 * π / 4) - Fk (17 * π / 8) (8 * π / 4)
      = 2 / 17 + (1 / π) * (-64*Real.sqrt 2/289) + (1 / π) ^ 2 * (32*Real.sqrt 2/289 - 64/289) := by
    unfold Fk; rw [sa, ca, sb, cb]; field_simp; ring
  rw [key]
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ := num_atoms
  nlinarith

theorem piece9 : (0.065346 : ℝ) ≤ Fk (19 * π / 8) (10 * π / 4) - Fk (19 * π / 8) (9 * π / 4) := by
  obtain ⟨sa, ca⟩ := sc9
  obtain ⟨sb, cb⟩ := sc10
  have key : Fk (19 * π / 8) (10 * π / 4) - Fk (19 * π / 8) (9 * π / 4)
      = 2 / 19 + (1 / π) * (80*Real.sqrt 2/361 - 144/361) + (1 / π) ^ 2 * (-32*Real.sqrt 2/361) := by
    unfold Fk; rw [sa, ca, sb, cb]; field_simp; ring
  rw [key]
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ := num_atoms
  nlinarith

theorem piece10 : (0.130212 : ℝ) ≤ Fk (21 * π / 8) (11 * π / 4) - Fk (21 * π / 8) (10 * π / 4) := by
  obtain ⟨sa, ca⟩ := sc10
  obtain ⟨sb, cb⟩ := sc11
  have key : Fk (21 * π / 8) (11 * π / 4) - Fk (21 * π / 8) (10 * π / 4)
      = 2 / 21 + (1 / π) * (176/441 - 80*Real.sqrt 2/441) + (1 / π) ^ 2 * (-32*Real.sqrt 2/441) := by
    unfold Fk; rw [sa, ca, sb, cb]; field_simp; ring
  rw [key]
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ := num_atoms
  nlinarith

theorem piece11 : (0.165056 : ℝ) ≤ Fk (23 * π / 8) (12 * π / 4) - Fk (23 * π / 8) (11 * π / 4) := by
  obtain ⟨sa, ca⟩ := sc11
  obtain ⟨sb, cb⟩ := sc12
  have key : Fk (23 * π / 8) (12 * π / 4) - Fk (23 * π / 8) (11 * π / 4)
      = 2 / 23 + (1 / π) * (96*Real.sqrt 2/529) + (1 / π) ^ 2 * (32*Real.sqrt 2/529 - 64/529) := by
    unfold Fk; rw [sa, ca, sb, cb]; field_simp; ring
  rw [key]
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ := num_atoms
  nlinarith
-- Cin( 1 π/2) >= 0.540836
-- Cin( 2 π/2) >= 1.621408
-- Cin( 3 π/2) >= 2.296504
-- Cin( 4 π/2) >= 2.408111
-- Cin( 5 π/2) >= 2.484841
-- Cin( 6 π/2) >= 2.780109
theorem cinc1 : (0.14925 : ℝ) ≤ Cin (1 * π / 4) := cin_quarter

theorem cinc2 : (0.540836 : ℝ) ≤ Cin (2 * π / 4) := by
  have h := cin_step (α := 1 * π / 4) (β := 2 * π / 4) (c := 3 * π / 8)
    (by positivity) (by linarith [Real.pi_pos]) (by positivity)
  linarith [cinc1, piece1]

theorem cinc3 : (1.080476 : ℝ) ≤ Cin (3 * π / 4) := by
  have h := cin_step (α := 2 * π / 4) (β := 3 * π / 4) (c := 5 * π / 8)
    (by positivity) (by linarith [Real.pi_pos]) (by positivity)
  linarith [cinc2, piece2]

theorem cinc4 : (1.621408 : ℝ) ≤ Cin (4 * π / 4) := by
  have h := cin_step (α := 3 * π / 4) (β := 4 * π / 4) (c := 7 * π / 8)
    (by positivity) (by linarith [Real.pi_pos]) (by positivity)
  linarith [cinc3, piece3]

theorem cinc5 : (2.044916 : ℝ) ≤ Cin (5 * π / 4) := by
  have h := cin_step (α := 4 * π / 4) (β := 5 * π / 4) (c := 9 * π / 8)
    (by positivity) (by linarith [Real.pi_pos]) (by positivity)
  linarith [cinc4, piece4]

theorem cinc6 : (2.296504 : ℝ) ≤ Cin (6 * π / 4) := by
  have h := cin_step (α := 5 * π / 4) (β := 6 * π / 4) (c := 11 * π / 8)
    (by positivity) (by linarith [Real.pi_pos]) (by positivity)
  linarith [cinc5, piece5]

theorem cinc7 : (2.394384 : ℝ) ≤ Cin (7 * π / 4) := by
  have h := cin_step (α := 6 * π / 4) (β := 7 * π / 4) (c := 13 * π / 8)
    (by positivity) (by linarith [Real.pi_pos]) (by positivity)
  linarith [cinc6, piece6]

theorem cinc8 : (2.408111 : ℝ) ≤ Cin (8 * π / 4) := by
  have h := cin_step (α := 7 * π / 4) (β := 8 * π / 4) (c := 15 * π / 8)
    (by positivity) (by linarith [Real.pi_pos]) (by positivity)
  linarith [cinc7, piece7]

theorem cinc9 : (2.419495 : ℝ) ≤ Cin (9 * π / 4) := by
  have h := cin_step (α := 8 * π / 4) (β := 9 * π / 4) (c := 17 * π / 8)
    (by positivity) (by linarith [Real.pi_pos]) (by positivity)
  linarith [cinc8, piece8]

theorem cinc10 : (2.484841 : ℝ) ≤ Cin (10 * π / 4) := by
  have h := cin_step (α := 9 * π / 4) (β := 10 * π / 4) (c := 19 * π / 8)
    (by positivity) (by linarith [Real.pi_pos]) (by positivity)
  linarith [cinc9, piece9]

theorem cinc11 : (2.615053 : ℝ) ≤ Cin (11 * π / 4) := by
  have h := cin_step (α := 10 * π / 4) (β := 11 * π / 4) (c := 21 * π / 8)
    (by positivity) (by linarith [Real.pi_pos]) (by positivity)
  linarith [cinc10, piece10]

theorem cinc12 : (2.780109 : ℝ) ≤ Cin (12 * π / 4) := by
  have h := cin_step (α := 11 * π / 4) (β := 12 * π / 4) (c := 23 * π / 8)
    (by positivity) (by linarith [Real.pi_pos]) (by positivity)
  linarith [cinc11, piece11]

theorem cin_val1 : (0.5408 : ℝ) ≤ Cin (π * 1 / 2) := by
  rw [show π * (1 : ℝ) / 2 = 2 * π / 4 by ring]; linarith [cinc2]

theorem cin_val2 : (1.6214 : ℝ) ≤ Cin (π * 2 / 2) := by
  rw [show π * (2 : ℝ) / 2 = 4 * π / 4 by ring]; linarith [cinc4]

theorem cin_val3 : (2.2965 : ℝ) ≤ Cin (π * 3 / 2) := by
  rw [show π * (3 : ℝ) / 2 = 6 * π / 4 by ring]; linarith [cinc6]

theorem cin_val4 : (2.4081 : ℝ) ≤ Cin (π * 4 / 2) := by
  rw [show π * (4 : ℝ) / 2 = 8 * π / 4 by ring]; linarith [cinc8]

theorem cin_val5 : (2.4848 : ℝ) ≤ Cin (π * 5 / 2) := by
  rw [show π * (5 : ℝ) / 2 = 10 * π / 4 by ring]; linarith [cinc10]

theorem cin_val6 : (2.7801 : ℝ) ≤ Cin (π * 6 / 2) := by
  rw [show π * (6 : ℝ) / 2 = 12 * π / 4 by ring]; linarith [cinc12]
/-! ### From `3π` on: the chain in closed form

On `[mπ/2, (m+1)π/2]` with `c = (2m+1)π/4`, `F_c(β) − F_c(α) = p₀ + p₁/π + p₂/π²` with rational `p`
(`piece_eq`). The needed instances are checked by kernel evaluation of the rational sums. -/

/-- `(sin(mπ/2), cos(mπ/2))`, as integers. -/
def scQ : ℕ → ℤ × ℤ
  | 0 => (0, 1)
  | m + 1 => ((scQ m).2, -(scQ m).1)

theorem sc_half (m : ℕ) :
    Real.sin (m * π / 2) = (scQ m).1 ∧ Real.cos (m * π / 2) = (scQ m).2 := by
  induction m with
  | zero => simp [scQ]
  | succ m ih =>
    rw [show ((m + 1 : ℕ) : ℝ) * π / 2 = m * π / 2 + π / 2 by push_cast; ring,
      Real.sin_add_pi_div_two, Real.cos_add_pi_div_two, ih.1, ih.2]
    simp [scQ]

/-- The gain of `cin_step` on `[mπ/2, (m+1)π/2]` at `c = (2m+1)π/4`, as `(p₀, p₁, p₂)` with value
`p₀ + p₁/π + p₂/π²`. -/
def pieceQ (m : ℕ) : ℚ × ℚ × ℚ :=
  (2 / (2 * m + 1), 8 * ((m + 1) * (scQ m).1 - m * (scQ (m + 1)).1) / (2 * m + 1) ^ 2,
    16 * ((scQ (m + 1)).2 - (scQ m).2) / (2 * m + 1) ^ 2)

/-- `p₀ + p₁/π + p₂/π²`. -/
def evalP (p : ℚ × ℚ × ℚ) : ℝ := p.1 + (1 / π) * p.2.1 + (1 / π) ^ 2 * p.2.2

theorem evalP_zero : evalP 0 = 0 := by simp [evalP]

theorem evalP_add (p q : ℚ × ℚ × ℚ) : evalP (p + q) = evalP p + evalP q := by
  simp only [evalP, Prod.fst_add, Prod.snd_add, Rat.cast_add]; ring

theorem piece_eq (m : ℕ) :
    Fk ((2 * m + 1) * π / 4) ((m + 1 : ℕ) * π / 2) - Fk ((2 * m + 1) * π / 4) (m * π / 2)
      = evalP (pieceQ m) := by
  obtain ⟨sa, ca⟩ := sc_half m
  obtain ⟨sb, cb⟩ := sc_half (m + 1)
  unfold Fk evalP pieceQ
  rw [sa, ca, sb, cb]
  have hπ := Real.pi_pos.ne'
  have hm : (2 * (m : ℝ) + 1) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- The summed gains over `m ∈ [6, N)`. -/
def sumQ (N : ℕ) : ℚ × ℚ × ℚ := ∑ m ∈ Finset.Ico 6 N, pieceQ m

/-- **The chain from `3π`**: `Cin(Nπ/2) ≥ Cin(3π) + Σ_{6 ≤ m < N} gain(m)`. -/
theorem cin_chain (N : ℕ) (hN : 6 ≤ N) : (2.780109 : ℝ) + evalP (sumQ N) ≤ Cin (N * π / 2) := by
  induction N, hN using Nat.le_induction with
  | base =>
    have e : sumQ 6 = 0 := by simp [sumQ]
    rw [e, evalP_zero, add_zero, show ((6 : ℕ) : ℝ) * π / 2 = 12 * π / 4 by push_cast; ring]
    exact cinc12
  | succ N hN ih =>
    have h6 : (6 : ℝ) ≤ N := by exact_mod_cast hN
    have h := cin_step (α := N * π / 2) (β := ((N + 1 : ℕ) : ℝ) * π / 2) (c := (2 * N + 1) * π / 4)
      (by nlinarith [Real.pi_pos]) (by push_cast; linarith [Real.pi_pos]) (by positivity)
    rw [piece_eq] at h
    rw [sumQ, Finset.sum_Ico_succ_top hN, ← sumQ, evalP_add]
    linarith

/-- A rational lower bound for `evalP`, from `0.3183097 < 1/π < 0.31831`. -/
def lowP (p : ℚ × ℚ × ℚ) : ℚ :=
  p.1 + (if 0 ≤ p.2.1 then 3183097 / 10 ^ 7 else 31831 / 10 ^ 5) * p.2.1
    + (if 0 ≤ p.2.2 then (3183097 / 10 ^ 7) ^ 2 else (31831 / 10 ^ 5) ^ 2) * p.2.2

theorem mul_le_of_bracket {q lo hi : ℚ} {x : ℝ} (hlo : (lo : ℝ) ≤ x) (hhi : x ≤ hi) :
    (((if 0 ≤ q then lo else hi) * q : ℚ) : ℝ) ≤ x * q := by
  split_ifs with h
  · have : (0 : ℝ) ≤ q := by exact_mod_cast h
    push_cast; nlinarith
  · have : (q : ℝ) < 0 := by exact_mod_cast not_le.1 h
    push_cast; nlinarith

theorem lowP_le (p : ℚ × ℚ × ℚ) : (lowP p : ℝ) ≤ evalP p := by
  obtain ⟨b1, b2, -, -, -, -, b7, b8, -, -⟩ := num_atoms
  have h1 := mul_le_of_bracket (q := p.2.1) (lo := 3183097 / 10 ^ 7) (hi := 31831 / 10 ^ 5)
    (x := 1 / π) (by push_cast; linarith) (by push_cast; linarith)
  have h2 := mul_le_of_bracket (q := p.2.2) (lo := (3183097 / 10 ^ 7) ^ 2)
    (hi := (31831 / 10 ^ 5) ^ 2) (x := (1 / π) ^ 2) (by push_cast; linarith) (by push_cast; linarith)
  unfold lowP evalP
  rw [Rat.cast_add, Rat.cast_add]
  linarith

theorem cin_of_check {N : ℕ} (hN : 6 ≤ N) {b : ℚ} (hb : b ≤ lowP (sumQ N)) :
    (2.780109 : ℝ) + b ≤ Cin (N * π / 2) := by
  have h1 := cin_chain N hN
  have h2 := lowP_le (sumQ N)
  have h3 : (b : ℝ) ≤ lowP (sumQ N) := by exact_mod_cast hb
  linarith

theorem cinH7 : (3.033953 : ℝ) ≤ Cin (14 * π / 4) := by
  have h := cin_of_check (N := 7) (by norm_num) (b := 253844 / 10 ^ 6) (by decide +kernel)
  rw [show ((7 : ℕ) : ℝ) * π / 2 = 14 * π / 4 by push_cast; ring] at h
  push_cast at h; linarith

theorem cinH11 : (3.453456 : ℝ) ≤ Cin (22 * π / 4) := by
  have h := cin_of_check (N := 11) (by norm_num) (b := 673347 / 10 ^ 6) (by decide +kernel)
  rw [show ((11 : ℕ) : ℝ) * π / 2 = 22 * π / 4 by push_cast; ring] at h
  push_cast at h; linarith

theorem cinH18 : (3.886992 : ℝ) ≤ Cin (36 * π / 4) := by
  have h := cin_of_check (N := 18) (by norm_num) (b := 1106883 / 10 ^ 6) (by decide +kernel)
  rw [show ((18 : ℕ) : ℝ) * π / 2 = 36 * π / 4 by push_cast; ring] at h
  push_cast at h; linarith

theorem cinH21 : (4.012087 : ℝ) ≤ Cin (42 * π / 4) := by
  have h := cin_of_check (N := 21) (by norm_num) (b := 1231978 / 10 ^ 6) (by decide +kernel)
  rw [show ((21 : ℕ) : ℝ) * π / 2 = 42 * π / 4 by push_cast; ring] at h
  push_cast at h; linarith

theorem cinH25 : (4.191228 : ℝ) ≤ Cin (50 * π / 4) := by
  have h := cin_of_check (N := 25) (by norm_num) (b := 1411119 / 10 ^ 6) (by decide +kernel)
  rw [show ((25 : ℕ) : ℝ) * π / 2 = 50 * π / 4 by push_cast; ring] at h
  push_cast at h; linarith

theorem cinH30 : (4.398497 : ℝ) ≤ Cin (60 * π / 4) := by
  have h := cin_of_check (N := 30) (by norm_num) (b := 1618388 / 10 ^ 6) (by decide +kernel)
  rw [show ((30 : ℕ) : ℝ) * π / 2 = 60 * π / 4 by push_cast; ring] at h
  push_cast at h; linarith

theorem cinH61 : (5.098076 : ℝ) ≤ Cin (122 * π / 4) := by
  have h := cin_of_check (N := 61) (by norm_num) (b := 2317967 / 10 ^ 6) (by decide +kernel)
  rw [show ((61 : ℕ) : ℝ) * π / 2 = 122 * π / 4 by push_cast; ring] at h
  push_cast at h; linarith

/-! ## E. The mode masses -/

theorem integrable_mul₂ {f h : ℝ → ℝ} (hf : MemLp f 2 volume) (hh : MemLp h 2 volume) :
    Integrable (fun t => f t * h t) := by
  simpa using integrable_mul_shift₂ hf hh 0

/-- A quadratic `A s² − 2Bs + C ≥ 0` for all `s`, with `A ≥ 0`, has `B² ≤ AC`. -/
theorem disc_le {A B C : ℝ} (hA : 0 ≤ A) (h : ∀ s : ℝ, 0 ≤ A * s ^ 2 - 2 * B * s + C) :
    B ^ 2 ≤ A * C := by
  rcases hA.lt_or_eq with hA | hA
  · have := h (B / A)
    have e : A * (B / A) ^ 2 - 2 * B * (B / A) + C = C - B ^ 2 / A := by field_simp; ring
    rw [e, sub_nonneg, div_le_iff₀ hA] at this
    linarith
  · subst hA
    have hC : 0 ≤ C := by simpa using h 0
    by_contra hB
    have hB0 : B ≠ 0 := by intro h0; apply hB; rw [h0]; simp
    have := h ((C + 1) / (2 * B))
    have e : 0 * ((C + 1) / (2 * B)) ^ 2 - 2 * B * ((C + 1) / (2 * B)) + C = -1 := by
      field_simp; ring
    linarith

/-- **Cauchy–Schwarz against a continuous function on `[−a, a]`.** -/
theorem cs_supp {a : ℝ} (ha : 0 < a) {g : ℝ → ℝ} (hp : Probe a g) {h : ℝ → ℝ} (hh : Continuous h) :
    (∫ t, g t * h t) ^ 2 ≤ normSq g * ∫ t in (-a)..a, h t ^ 2 := by
  set hI := (Icc (-a) a).indicator h with hhI
  have hmem : MemLp hI 2 volume := by
    obtain ⟨C, hC⟩ := (isCompact_Icc (a := -a) (b := a)).exists_bound_of_continuousOn
      hh.continuousOn
    exact memLp_indicator_of_continuous hh measurableSet_Icc measure_Icc_lt_top.ne
      (C := C) fun x hx => by simpa [Real.norm_eq_abs] using hC x hx
  have e1 : (∫ t, g t * h t) = ∫ t, g t * hI t := by
    congr 1; funext t
    by_cases ht : t ∈ Icc (-a) a
    · simp [hhI, ht]
    · have : a < |t| := by
        simp only [mem_Icc, not_and_or, not_le] at ht
        rcases ht with h' | h'
        · rw [abs_of_neg (by linarith)]; linarith
        · rw [abs_of_pos (by linarith)]; exact h'
      simp [hp.supp t this]
  have e2 : (∫ t in (-a)..a, h t ^ 2) = ∫ t, hI t ^ 2 := by
    rw [intervalIntegral.integral_of_le (by linarith), ← integral_Icc_eq_integral_Ioc,
      ← integral_indicator measurableSet_Icc]
    congr 1; funext t
    by_cases ht : t ∈ Icc (-a) a <;> simp [hhI, ht]
  rw [e1, e2]
  have iG := hp.memL2.integrable_sq
  have iH := hmem.integrable_sq
  have iGH := integrable_mul₂ hp.memL2 hmem
  refine disc_le (normSq_nonneg g) fun s => ?_
  have hq : 0 ≤ ∫ t, (s * g t - hI t) ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have e3 : (∫ t, (s * g t - hI t) ^ 2)
      = normSq g * s ^ 2 - 2 * (∫ t, g t * hI t) * s + ∫ t, hI t ^ 2 := by
    have i1 : Integrable (fun t => s ^ 2 * g t ^ 2) := iG.const_mul _
    have i2 : Integrable (fun t => 2 * s * (g t * hI t)) := iGH.const_mul _
    have i3 : Integrable (fun t => s ^ 2 * g t ^ 2 - 2 * s * (g t * hI t)) := i1.sub i2
    have ef : (fun t => (s * g t - hI t) ^ 2)
        = fun t => s ^ 2 * g t ^ 2 - 2 * s * (g t * hI t) + hI t ^ 2 := by funext t; ring
    rw [ef, integral_add i3 iH, integral_sub i1 i2, integral_const_mul, integral_const_mul]
    unfold normSq; ring
  rw [e3] at hq; exact hq

/-- For even `g`, the Fourier coefficient is real: `c_n = X_n/(8a)`, `X_n = ∫ g cos(πnt/4a)`. -/
theorem cf_even {a : ℝ} (ha : 0 < a) {g : ℝ → ℝ} (hp : Probe a g) (n : ℤ) :
    cf (2 * a) g n = (((1 / (8 * a)) * ∫ t, g t * Real.cos (π * n * t / (4 * a)) : ℝ) : ℂ) := by
  unfold cf
  push_cast
  have hsuppC : ∀ u, a < |u| →
      Complex.exp (-(2 * π * I * n * u / (4 * (2 * a)))) * ((g u : ℝ) : ℂ) = 0 := fun u hu => by
    rw [hp.supp u hu]; simp
  rw [integral_eq_of_supp hsuppC (by linarith) (by linarith)]
  have hpt : ∀ t : ℝ, Complex.exp (-(2 * π * I * n * t / (4 * (2 * a)))) * ((g t : ℝ) : ℂ)
      = ((g t * Real.cos (π * n * t / (4 * a)) : ℝ) : ℂ)
        - I * ((g t * Real.sin (π * n * t / (4 * a)) : ℝ) : ℂ) := by
    intro t
    have e : -(2 * π * I * n * t / (4 * (2 * a))) = ((-(π * n * t / (4 * a)) : ℝ) : ℂ) * I := by
      push_cast; field_simp
    rw [e, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg,
      Real.sin_neg]
    push_cast; ring
  simp_rw [hpt]
  have hI := probe_integrable hp
  have ic : Integrable (fun t => g t * Real.cos (π * n * t / (4 * a))) :=
    hI.mul_bdd (c := 1)
      (show Continuous (fun t : ℝ => Real.cos (π * n * t / (4 * a))) by fun_prop).aestronglyMeasurable
      (Eventually.of_forall fun t => by rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _)
  have is : Integrable (fun t => g t * Real.sin (π * n * t / (4 * a))) :=
    hI.mul_bdd (c := 1)
      (show Continuous (fun t : ℝ => Real.sin (π * n * t / (4 * a))) by fun_prop).aestronglyMeasurable
      (Eventually.of_forall fun t => by rw [Real.norm_eq_abs]; exact Real.abs_sin_le_one _)
  have hsin : (∫ t, g t * Real.sin (π * n * t / (4 * a))) = 0 := by
    have h := integral_neg_eq_self (fun t => g t * Real.sin (π * n * t / (4 * a))) volume
    have e : (fun t => g (-t) * Real.sin (π * n * -t / (4 * a)))
        = fun t => -(g t * Real.sin (π * n * t / (4 * a))) := by
      funext t; rw [hp.even, show π * n * -t / (4 * a) = -(π * n * t / (4 * a)) by ring,
        Real.sin_neg]; ring
    rw [e, integral_neg] at h; linarith
  have i1 : Integrable (fun x : ℝ => ((g x * Real.cos (π * n * x / (4 * a)) : ℝ) : ℂ)) := ic.ofReal
  have i2 : Integrable (fun x : ℝ => I * ((g x * Real.sin (π * n * x / (4 * a)) : ℝ) : ℂ)) :=
    is.ofReal.const_mul I
  rw [integral_sub i1 i2, integral_const_mul, integral_complex_ofReal,
    integral_complex_ofReal, hsin]
  push_cast; ring

theorem pm_even {a : ℝ} (ha : 0 < a) {g : ℝ → ℝ} (hp : Probe a g) (n : ℤ) :
    pm a g n = (∫ t, g t * Real.cos (π * n * t / (4 * a))) ^ 2 / (8 * a) := by
  unfold pm; rw [cf_even ha hp, Complex.norm_real, Real.norm_eq_abs, sq_abs]; field_simp


theorem integral_supp {a : ℝ} (ha : 0 < a) {g : ℝ → ℝ} (hp : Probe a g) (h : ℝ → ℝ) :
    (∫ t, g t * h t) = ∫ t in (-a)..a, g t * h t := by
  rw [intervalIntegral.integral_of_le (by linarith), ← integral_Icc_eq_integral_Ioc,
    setIntegral_eq_integral_of_forall_compl_eq_zero]
  intro t ht
  simp only [mem_Icc, not_and_or, not_le] at ht
  have : a < |t| := by
    rcases ht with h' | h'
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; exact h'
  rw [hp.supp t this, zero_mul]

/-- **Orthogonality to `w` makes `∫ g` tiny**: `(∫ g)² ≤ a⁵/30` for `a ≤ 1/2`. -/
theorem integral_sq_perp {a : ℝ} (ha : 0 < a) (ha2 : a ≤ 1 / 2) {g : ℝ → ℝ} (hp : Probe a g)
    (hn : normSq g = 1) (h0 : poleR g a = 0) : (∫ t, g t) ^ 2 ≤ a ^ 5 / 30 := by
  have hI := probe_integrable hp
  have iiG := memLp_intervalIntegrable hp.memL2 (-a) a
  have iS : IntervalIntegrable (fun t => g t * Real.sinh (t / 2)) volume (-a) a :=
    iiG.mul_continuousOn (by fun_prop)
  have iC : IntervalIntegrable (fun t => g t * Real.cosh (t / 2)) volume (-a) a :=
    iiG.mul_continuousOn (by fun_prop)
  have hsinh : (∫ t in (-a)..a, g t * Real.sinh (t / 2)) = 0 := by
    have h := intervalIntegral.integral_comp_neg (a := -a) (b := a)
      (fun t => g t * Real.sinh (t / 2))
    have e : (fun t => g (-t) * Real.sinh (-t / 2)) = fun t => -(g t * Real.sinh (t / 2)) := by
      funext t; rw [hp.even, neg_div, Real.sinh_neg]; ring
    rw [e, intervalIntegral.integral_neg, neg_neg] at h; linarith
  have hcosh : (∫ t in (-a)..a, g t * Real.cosh (t / 2)) = 0 := by
    have e : poleR g a = (∫ t in (-a)..a, g t * Real.cosh (t / 2))
        - ∫ t in (-a)..a, g t * Real.sinh (t / 2) := by
      unfold poleR
      rw [← intervalIntegral.integral_sub iC iS]
      refine intervalIntegral.integral_congr fun t _ => ?_
      rw [show Real.exp (-(t / 2)) = Real.cosh (t / 2) - Real.sinh (t / 2) by
        rw [Real.cosh_eq, Real.sinh_eq]; ring]
      ring
    rw [h0, hsinh, sub_zero] at e; exact e.symm
  have iOne : IntervalIntegrable (fun t => g t * (1 - Real.cosh (t / 2))) volume (-a) a :=
    iiG.mul_continuousOn (by fun_prop)
  have hg1 : (∫ t, g t) = ∫ t, g t * (1 - Real.cosh (t / 2)) := by
    rw [integral_supp ha hp (fun t => 1 - Real.cosh (t / 2))]
    have e0 : (∫ t, g t) = ∫ t, g t * 1 := by simp
    rw [e0, integral_supp ha hp (fun _ => 1)]
    have e2 : (∫ t in (-a)..a, g t * 1)
        = (∫ t in (-a)..a, g t * (1 - Real.cosh (t / 2))) + ∫ t in (-a)..a, g t * Real.cosh (t / 2) := by
      rw [← intervalIntegral.integral_add iOne iC]
      refine intervalIntegral.integral_congr fun t _ => ?_
      ring
    rw [e2, hcosh, add_zero]
  have hcs := cs_supp ha hp (h := fun t => 1 - Real.cosh (t / 2)) (by fun_prop)
  rw [← hg1, hn, one_mul] at hcs
  set M := a ^ 2 / 8 + 5 * a ^ 4 / 1536 with hM
  have hpt : ∀ t ∈ Icc (-a) a, (1 - Real.cosh (t / 2)) ^ 2 ≤ M ^ 2 := by
    intro t ht
    have hta : |t| ≤ a := abs_le.2 ⟨ht.1, ht.2⟩
    have ht2 : t ^ 2 ≤ a ^ 2 := by nlinarith [sq_abs t, abs_nonneg t]
    have hc1 := Real.one_le_cosh (t / 2)
    have hc2 := cosh_le_taylor (y := t / 2) (by rw [abs_div, abs_two]; linarith)
    have ht4 : t ^ 4 ≤ a ^ 4 := by nlinarith [sq_nonneg t, sq_nonneg a]
    have hup : Real.cosh (t / 2) - 1 ≤ M := by
      rw [hM]; nlinarith
    have hM0 : 0 ≤ M := by positivity
    nlinarith
  have hmono := intervalIntegral.integral_mono_on (by linarith : -a ≤ a)
    ((by fun_prop : Continuous (fun t : ℝ => (1 - Real.cosh (t / 2)) ^ 2)).intervalIntegrable _ _)
    (intervalIntegrable_const (μ := volume) (c := M ^ 2)) hpt
  rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
  have hfin : (a - -a) * M ^ 2 ≤ a ^ 5 / 30 := by
    rw [hM]
    have h1 : 5 * a ^ 2 / 192 ≤ 5 / 768 := by nlinarith
    have e : (a - -a) * (a ^ 2 / 8 + 5 * a ^ 4 / 1536) ^ 2
        = a ^ 5 / 32 * (1 + 5 * a ^ 2 / 192) ^ 2 := by ring
    rw [e]
    have h2 : (1 + 5 * a ^ 2 / 192) ^ 2 ≤ (1 + 5 / 768) ^ 2 := by
      have : 0 ≤ 5 * a ^ 2 / 192 := by positivity
      nlinarith
    have h5 : 0 < a ^ 5 := by positivity
    nlinarith
  linarith

/-- `∫_{−a}^{a} (cos(πnt/4a) − β)² = a(1 + 2 sin(πn/2)/(πn) − 16β sin(πn/4)/(πn) + 2β²)`. -/
theorem integral_cos_sub_sq {a : ℝ} (ha : 0 < a) {n : ℤ} (hn : 0 < n) (β : ℝ) :
    (∫ t in (-a)..a, (Real.cos (π * n * t / (4 * a)) - β) ^ 2)
      = a * (1 + 2 * Real.sin (π * n / 2) / (π * n) - 16 * β * Real.sin (π * n / 4) / (π * n)
          + 2 * β ^ 2) := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  set ω := π * n / (4 * a) with hω
  have hω0 : 0 < ω := by positivity
  have hcosint : ∀ c : ℝ, 0 < c → (∫ t in (-a)..a, Real.cos (c * t)) = 2 * Real.sin (c * a) / c := by
    intro c hc
    rw [intervalIntegral.integral_comp_mul_left (fun s => Real.cos s) hc.ne', integral_cos,
      smul_eq_mul, show c * -a = -(c * a) by ring, Real.sin_neg]
    field_simp; ring
  have e : (fun t => (Real.cos (π * n * t / (4 * a)) - β) ^ 2)
      = fun t => 1 / 2 + Real.cos ((2 * ω) * t) / 2 - 2 * β * Real.cos (ω * t) + β ^ 2 := by
    funext t
    rw [show π * n * t / (4 * a) = ω * t by rw [hω]; ring, sub_sq, Real.cos_sq,
      show 2 * (ω * t) = (2 * ω) * t by ring]
    ring
  rw [e]
  have c1 : Continuous (fun t => Real.cos ((2 * ω) * t) / 2) := by fun_prop
  have c2 : Continuous (fun t => 2 * β * Real.cos (ω * t)) := by fun_prop
  have i0 : IntervalIntegrable (fun _ : ℝ => (1 / 2 : ℝ)) volume (-a) a := intervalIntegrable_const
  have i3 : IntervalIntegrable (fun _ : ℝ => β ^ 2) volume (-a) a := intervalIntegrable_const
  have hsplit : (∫ t in (-a)..a, (1 / 2 + Real.cos ((2 * ω) * t) / 2 - 2 * β * Real.cos (ω * t) + β ^ 2))
      = (∫ t in (-a)..a, (1 / 2 : ℝ)) + (∫ t in (-a)..a, Real.cos ((2 * ω) * t) / 2)
        - (∫ t in (-a)..a, 2 * β * Real.cos (ω * t)) + ∫ t in (-a)..a, β ^ 2 := by
    rw [intervalIntegral.integral_add ((i0.add (c1.intervalIntegrable _ _)).sub
      (c2.intervalIntegrable _ _)) i3, intervalIntegral.integral_sub
      (i0.add (c1.intervalIntegrable _ _)) (c2.intervalIntegrable _ _),
      intervalIntegral.integral_add i0 (c1.intervalIntegrable _ _)]
  have p1 : (∫ t in (-a)..a, Real.cos ((2 * ω) * t) / 2) = Real.sin (π * n / 2) / (2 * ω) := by
    rw [intervalIntegral.integral_div, hcosint _ (by positivity),
      show 2 * ω * a = π * n / 2 by rw [hω]; field_simp; ring]
    field_simp
  have p2 : (∫ t in (-a)..a, 2 * β * Real.cos (ω * t)) = 2 * β * (2 * Real.sin (π * n / 4) / ω) := by
    rw [intervalIntegral.integral_const_mul, hcosint _ hω0,
      show ω * a = π * n / 4 by rw [hω]; field_simp]
  rw [hsplit, p1, p2]
  simp only [intervalIntegral.integral_const, smul_eq_mul]
  rw [hω]; field_simp; ring

/-- **Mode-mass bound**: `p_n ≤ (1.05·∫(cos − β)² + 21β²(∫g)²)/(8a)`. -/
theorem pm_le {a : ℝ} (ha : 0 < a) {g : ℝ → ℝ} (hp : Probe a g) (hn : normSq g = 1) (n : ℤ)
    (β : ℝ) :
    pm a g n ≤ (1.05 * (∫ t in (-a)..a, (Real.cos (π * n * t / (4 * a)) - β) ^ 2)
      + 21 * β ^ 2 * (∫ t, g t) ^ 2) / (8 * a) := by
  rw [pm_even ha hp]
  have hI := probe_integrable hp
  have ic : Integrable (fun t => g t * Real.cos (π * n * t / (4 * a))) :=
    hI.mul_bdd (c := 1)
      (show Continuous (fun t : ℝ => Real.cos (π * n * t / (4 * a))) by fun_prop).aestronglyMeasurable
      (Eventually.of_forall fun t => by rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _)
  have hY : (∫ t, g t * Real.cos (π * n * t / (4 * a)))
      = (∫ t, g t * (Real.cos (π * n * t / (4 * a)) - β)) + β * ∫ t, g t := by
    have i2 : Integrable (fun t => g t * β) := hI.mul_const β
    rw [show (fun t => g t * (Real.cos (π * n * t / (4 * a)) - β))
        = fun t => g t * Real.cos (π * n * t / (4 * a)) - g t * β by funext t; ring,
      integral_sub ic i2, integral_mul_const]
    ring
  have hcs := cs_supp ha hp (h := fun t => Real.cos (π * n * t / (4 * a)) - β) (by fun_prop)
  rw [hn, one_mul] at hcs
  rw [hY]
  set Y := ∫ t, g t * (Real.cos (π * n * t / (4 * a)) - β)
  set Z := β * ∫ t, g t
  have h8 : 0 < 8 * a := by linarith
  apply div_le_div_of_nonneg_right _ h8.le
  have hZ : Z ^ 2 = β ^ 2 * (∫ t, g t) ^ 2 := by simp only [Z]; ring
  nlinarith [sq_nonneg (Y / 20 - Z)]

theorem pm_neg {a : ℝ} (ha : 0 < a) {g : ℝ → ℝ} (hp : Probe a g) (n : ℤ) :
    pm a g (-n) = pm a g n := by
  rw [pm_even ha hp, pm_even ha hp]; congr 3; funext t; push_cast
  rw [show π * -(n : ℝ) * t / (4 * a) = -(π * n * t / (4 * a)) by ring, Real.cos_neg]

theorem pm_zero_le {a : ℝ} (ha : 0 < a) (ha2 : a ≤ 1 / 2) {g : ℝ → ℝ} (hp : Probe a g)
    (hn : normSq g = 1) (h0 : poleR g a = 0) : pm a g 0 ≤ a ^ 4 / 240 := by
  rw [pm_even ha hp]
  simp only [Int.cast_zero, mul_zero, zero_mul, zero_div, Real.cos_zero, mul_one]
  have := integral_sq_perp ha ha2 hp hn h0
  rw [div_le_iff₀ (by linarith)]
  nlinarith [pow_pos ha 4]

theorem modeE_zero (a : ℝ) : modeE a 0 = 0 := by
  unfold modeE; simp

/-- The generic per-mode estimate `(ψ − τ)p ≥ (ψ̲ − τ)P`. -/
theorem term_ge {ψ ψl τ p P : ℝ} (h1 : ψl ≤ ψ) (h2 : ψl - τ ≤ 0) (h3 : 0 ≤ p) (h4 : p ≤ P) :
    (ψl - τ) * P ≤ (ψ - τ) * p := by nlinarith

/-- `err(a) ≥ 0`. -/
theorem errK_nonneg {a : ℝ} (ha : 0 ≤ a) : 0 ≤ errK a := by unfold errK; positivity

/-- **Mode-mass bound from one constant**: if `1 + 2 sin(πk/2)/(πk) − 16β sin(πk/4)/(πk) + 2β² ≤ C`
and `a ≤ A ≤ ½`, then `p_k ≤ (1.05·C + 21β²A⁴/30)/8` (`pm_le` with `(∫g)² ≤ a⁵/30`). -/
theorem pm_le_of {a A : ℝ} (ha : 0 < a) (ha2 : a ≤ A) (hA : A ≤ 1 / 2) {g : ℝ → ℝ} (hp : Probe a g)
    (hn : normSq g = 1) (h0 : poleR g a = 0) {k : ℤ} (hk : 0 < k) {β C : ℝ}
    (hc : 1 + 2 * Real.sin (π * k / 2) / (π * k) - 16 * β * Real.sin (π * k / 4) / (π * k)
      + 2 * β ^ 2 ≤ C) :
    pm a g k ≤ (1.05 * C + 21 * β ^ 2 * A ^ 4 / 30) / 8 := by
  have h1 := pm_le ha hp hn k β
  rw [integral_cos_sub_sq ha hk β] at h1
  have hI := integral_sq_perp ha (by linarith) hp hn h0
  refine h1.trans ?_
  rw [div_le_iff₀ (by linarith : (0 : ℝ) < 8 * a)]
  have e1 := mul_le_mul_of_nonneg_left hc ha.le
  have e2 := mul_le_mul_of_nonneg_left hI (sq_nonneg β)
  have e3 : β ^ 2 * (a ^ 5 / 30) ≤ β ^ 2 * (a * A ^ 4 / 30) := by
    have : a ^ 4 ≤ A ^ 4 := pow_le_pow_left₀ ha.le ha2 4
    have : a * a ^ 4 ≤ a * A ^ 4 := mul_le_mul_of_nonneg_left this ha.le
    have e : a ^ 5 = a * a ^ 4 := by ring
    rw [e]; gcongr
  nlinarith

/-- **One low mode**: from `Cin(πk/2) ≥ C_v`, `1 − 2 sin(πk/2)/(πk) ≥ D`, `Y ≤ X` and `p_k ≤ P`,
with `ψ̲ = C_v + aD − err(a) − X ≤ τ`: `(ψ̲ − τ)P ≤ (ψ_k − Y − τ)p_k`. -/
theorem term_mode {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) {g : ℝ → ℝ} {k : ℤ} (hk : 0 < k)
    {Cv D X Y τ P : ℝ} (hcv : Cv ≤ Cin (π * k / 2))
    (hd : D ≤ 1 - 2 * Real.sin (π * k / 2) / (π * k)) (hY : Y ≤ X)
    (hneg : Cv + a * D - errK a - X - τ ≤ 0) (hP : pm a g k ≤ P) :
    (Cv + a * D - errK a - X - τ) * P ≤ (modeE a k - Y - τ) * pm a g k :=
  term_ge (by linarith [modeE_ge ha ha1 hk, mul_le_mul_of_nonneg_left hd ha.le]) hneg
    (pm_nonneg ha g k) hP

theorem cval1 : 1 + 2 * Real.sin (π * ((1 : ℤ) : ℝ) / 2) / (π * ((1 : ℤ) : ℝ))
    - 16 * (0.9 : ℝ) * Real.sin (π * ((1 : ℤ) : ℝ) / 4) / (π * ((1 : ℤ) : ℝ)) + 2 * (0.9 : ℝ) ^ 2
    ≤ (0.01551 : ℝ) := by
  push_cast
  rw [show π * (1 : ℝ) / 2 = 2 * π / 4 by ring, show π * (1 : ℝ) / 4 = 1 * π / 4 by ring,
    (sc2).1, (sc1).1]
  have key : 1 + 2 * (1) / (π * 1) - 16 * (0.9 : ℝ) * (Real.sqrt 2/2) / (π * 1)
      + 2 * (0.9 : ℝ) ^ 2 = 1 + 2 * (0.9 : ℝ) ^ 2 + (1 / π) * (2 - 36*Real.sqrt 2/5) := by
    field_simp; ring
  rw [key]
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ := num_atoms
  nlinarith

theorem pm_le1 {a : ℝ} (ha : 0 < a) (ha2 : a ≤ 0.3466) {g : ℝ → ℝ} (hp : Probe a g)
    (hn : normSq g = 1) (h0 : poleR g a = 0) : pm a g 1 ≤ (0.00306 : ℝ) :=
  (pm_le_of ha ha2 (by norm_num) hp hn h0 (by norm_num) cval1).trans (by norm_num)

theorem cval2 : 1 + 2 * Real.sin (π * ((2 : ℤ) : ℝ) / 2) / (π * ((2 : ℤ) : ℝ))
    - 16 * (0.6366 : ℝ) * Real.sin (π * ((2 : ℤ) : ℝ) / 4) / (π * ((2 : ℤ) : ℝ)) + 2 * (0.6366 : ℝ) ^ 2
    ≤ (0.18946 : ℝ) := by
  push_cast
  rw [show π * (2 : ℝ) / 2 = 4 * π / 4 by ring, show π * (2 : ℝ) / 4 = 2 * π / 4 by ring,
    (sc4).1, (sc2).1]
  have key : 1 + 2 * (0) / (π * 2) - 16 * (0.6366 : ℝ) * (1) / (π * 2)
      + 2 * (0.6366 : ℝ) ^ 2 = 1 + 2 * (0.6366 : ℝ) ^ 2 + (1 / π) * (-3183/625) := by
    field_simp; ring
  rw [key]
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ := num_atoms
  nlinarith

theorem pm_le2 {a : ℝ} (ha : 0 < a) (ha2 : a ≤ 0.3466) {g : ℝ → ℝ} (hp : Probe a g)
    (hn : normSq g = 1) (h0 : poleR g a = 0) : pm a g 2 ≤ (0.02538 : ℝ) :=
  (pm_le_of ha ha2 (by norm_num) hp hn h0 (by norm_num) cval2).trans (by norm_num)

theorem cval3 : 1 + 2 * Real.sin (π * ((3 : ℤ) : ℝ) / 2) / (π * ((3 : ℤ) : ℝ))
    - 16 * (0.3 : ℝ) * Real.sin (π * ((3 : ℤ) : ℝ) / 4) / (π * ((3 : ℤ) : ℝ)) + 2 * (0.3 : ℝ) ^ 2
    ≤ (0.60769 : ℝ) := by
  push_cast
  rw [show π * (3 : ℝ) / 2 = 6 * π / 4 by ring, show π * (3 : ℝ) / 4 = 3 * π / 4 by ring,
    (sc6).1, (sc3).1]
  have key : 1 + 2 * (-1) / (π * 3) - 16 * (0.3 : ℝ) * (Real.sqrt 2/2) / (π * 3)
      + 2 * (0.3 : ℝ) ^ 2 = 1 + 2 * (0.3 : ℝ) ^ 2 + (1 / π) * (-4*Real.sqrt 2/5 - 2/3) := by
    field_simp; ring
  rw [key]
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ := num_atoms
  nlinarith

theorem pm_le3 {a : ℝ} (ha : 0 < a) (ha2 : a ≤ 0.3466) {g : ℝ → ℝ} (hp : Probe a g)
    (hn : normSq g = 1) (h0 : poleR g a = 0) : pm a g 3 ≤ (0.07988 : ℝ) :=
  (pm_le_of ha ha2 (by norm_num) hp hn h0 (by norm_num) cval3).trans (by norm_num)

theorem cval4 : 1 + 2 * Real.sin (π * ((4 : ℤ) : ℝ) / 2) / (π * ((4 : ℤ) : ℝ))
    - 16 * (0 : ℝ) * Real.sin (π * ((4 : ℤ) : ℝ) / 4) / (π * ((4 : ℤ) : ℝ)) + 2 * (0 : ℝ) ^ 2
    ≤ (1 : ℝ) := by
  push_cast
  rw [show π * (4 : ℝ) / 2 = 8 * π / 4 by ring, show π * (4 : ℝ) / 4 = 4 * π / 4 by ring,
    (sc8).1, (sc4).1]
  have key : 1 + 2 * (0) / (π * 4) - 16 * (0 : ℝ) * (0) / (π * 4)
      + 2 * (0 : ℝ) ^ 2 = 1 + 2 * (0 : ℝ) ^ 2 + (1 / π) * (0) := by
    field_simp; ring
  rw [key]
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ := num_atoms
  nlinarith

theorem pm_le4 {a : ℝ} (ha : 0 < a) (ha2 : a ≤ 0.3466) {g : ℝ → ℝ} (hp : Probe a g)
    (hn : normSq g = 1) (h0 : poleR g a = 0) : pm a g 4 ≤ (0.13125 : ℝ) :=
  (pm_le_of ha ha2 (by norm_num) hp hn h0 (by norm_num) cval4).trans (by norm_num)

theorem cval5 : 1 + 2 * Real.sin (π * ((5 : ℤ) : ℝ) / 2) / (π * ((5 : ℤ) : ℝ))
    - 16 * (-0.18 : ℝ) * Real.sin (π * ((5 : ℤ) : ℝ) / 4) / (π * ((5 : ℤ) : ℝ)) + 2 * (-0.18 : ℝ) ^ 2
    ≤ (1.0625 : ℝ) := by
  push_cast
  rw [show π * (5 : ℝ) / 2 = 10 * π / 4 by ring, show π * (5 : ℝ) / 4 = 5 * π / 4 by ring,
    (sc10).1, (sc5).1]
  have key : 1 + 2 * (1) / (π * 5) - 16 * (-0.18 : ℝ) * (-Real.sqrt 2/2) / (π * 5)
      + 2 * (-0.18 : ℝ) ^ 2 = 1 + 2 * (-0.18 : ℝ) ^ 2 + (1 / π) * (2/5 - 36*Real.sqrt 2/125) := by
    field_simp; ring
  rw [key]
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ := num_atoms
  nlinarith

theorem pm_le5 {a : ℝ} (ha : 0 < a) (ha2 : a ≤ 0.3466) {g : ℝ → ℝ} (hp : Probe a g)
    (hn : normSq g = 1) (h0 : poleR g a = 0) : pm a g 5 ≤ (0.1395 : ℝ) :=
  (pm_le_of ha ha2 (by norm_num) hp hn h0 (by norm_num) cval5).trans (by norm_num)

/-! ## F. The box, and the gap below the first prime -/

theorem nearField_box_le' {a : ℝ} (ha : 0 < a) :
    (∫ u in Ioc 0 (2 * a), archIntegrand (box a) u) ≤ 1 + a / 2 := by
  have hpt : ∀ u ∈ Ioc 0 (2 * a), archIntegrand (box a) u ≤ 1 / (2 * a) + u / (4 * a) := by
    intro u hu
    have hK0 : 0 ≤ kerK u := (kerK_pos hu.1).le
    have h1 : archIntegrand (box a) u ≤ (1 / (2 * a) * u) * kerK u := by
      unfold archIntegrand
      rw [← box_sq ha]
      exact mul_le_mul_of_nonneg_right (box_autocorr_diff_le hu.1) hK0
    have h2 : (1 / (2 * a) * u) * kerK u ≤ (1 / (2 * a) * u) * (1 / u + 1 / 2) :=
      mul_le_mul_of_nonneg_left (kerK_le' hu.1) (by have := hu.1; positivity)
    have h3 : (1 / (2 * a) * u) * (1 / u + 1 / 2) = 1 / (2 * a) + u / (4 * a) := by
      field_simp [hu.1.ne']; ring
    linarith
  have hc : Continuous (fun u : ℝ => 1 / (2 * a) + u / (4 * a)) := by fun_prop
  have hmono := setIntegral_mono_on ((box_probe a).arch.mono_set Ioc_subset_Ioi_self)
    (hc.integrableOn_Ioc) measurableSet_Ioc hpt
  have hR : (∫ u in Ioc 0 (2 * a), (1 / (2 * a) + u / (4 * a))) = 1 + a / 2 := by
    rw [← intervalIntegral.integral_of_le (by linarith), intervalIntegral.integral_add
      intervalIntegrable_const
      ((by fun_prop : Continuous (fun u : ℝ => u / (4 * a))).intervalIntegrable _ _),
      intervalIntegral.integral_const, intervalIntegral.integral_div, integral_id, smul_eq_mul]
    field_simp; ring
  linarith

theorem pole_box_le {a : ℝ} (ha : 0 < a) (ha2 : a ≤ 2) :
    2 * poleR (box a) a ^ 2 ≤ 4 * a * (1 + a ^ 2 / 24 + a ^ 4 / 1600) ^ 2 := by
  set c := 1 / Real.sqrt (2 * a) with hc
  have hp : poleR (box a) a = c * ∫ u in (-a)..a, Real.exp (-(u / 2)) := by
    unfold poleR
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [uIcc_of_le (by linarith)] at hu
    simp only [box_apply, abs_le.2 ⟨hu.1, hu.2⟩, ite_true, hc]
  have hint : (∫ u in (-a)..a, Real.exp (-(u / 2))) = 4 * Real.sinh (a / 2) := by
    have h := intervalIntegral.integral_comp_mul_left (a := -a) (b := a) (fun s => Real.exp s)
      (show (-(1 / 2) : ℝ) ≠ 0 by norm_num)
    rw [show (fun u => Real.exp (-(u / 2))) = fun u => Real.exp (-(1 / 2) * u) by
      funext u; ring_nf, h, integral_exp, Real.sinh_eq, smul_eq_mul]
    ring_nf
  have hs := sinh_le_taylor (y := a / 2) (by linarith) (by linarith)
  have hs0 : 0 ≤ Real.sinh (a / 2) := (Real.sinh_pos_iff.2 (by linarith)).le
  have hc2 : c ^ 2 = 1 / (2 * a) := box_sq ha
  rw [hp, hint]
  have e1 : 2 * (c * (4 * Real.sinh (a / 2))) ^ 2 = 16 * Real.sinh (a / 2) ^ 2 / a := by
    rw [mul_pow, mul_pow, hc2]; field_simp; ring
  rw [e1, div_le_iff₀ ha]
  have hb : Real.sinh (a / 2) ≤ a / 2 * (1 + a ^ 2 / 24 + a ^ 4 / 1600) := by
    have : a / 2 + (a / 2) ^ 3 / 6 + (a / 2) ^ 5 / 100 = a / 2 * (1 + a ^ 2 / 24 + a ^ 4 / 1600) := by
      ring
    linarith
  have := pow_le_pow_left₀ hs0 hb 2
  nlinarith


/-- `ψ_n ≥ Cin(πn/2) + a(1 − 0.31831/3) − err(a)` for `n ≥ 6`. -/
theorem modeE_tail_base {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) {n : ℤ} (hn : 6 ≤ n) :
    Cin (π * n / 2) + a * (1 - 0.31831 / 3) - errK a ≤ modeE a n := by
  have hnr : (6 : ℝ) ≤ n := by exact_mod_cast hn
  have hψ := modeE_ge ha ha1 (n := n) (by omega)
  have hπ := Real.pi_pos
  have h1 : 2 * Real.sin (π * n / 2) / (π * n) ≤ 2 / (π * n) :=
    div_le_div_of_nonneg_right (by linarith [Real.sin_le_one (π * n / 2)]) (by positivity)
  have h2 : 2 / (π * n) ≤ 2 / (π * 6) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) (by nlinarith)
  have h3 : 2 / (π * 6) = (1 / π) / 3 := by field_simp; ring
  obtain ⟨b1, b2, -⟩ := num_atoms
  nlinarith

/-- The tail level `τ(a) = 2.7801 + a(1 − 0.31831/3) − err(a)`. -/
def tauF (a : ℝ) : ℝ := 2.7801 + a * (1 - 0.31831 / 3) - errK a

theorem tail_ok {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) {n : ℤ} (hn : 6 ≤ n) : tauF a ≤ modeE a n := by
  have hnr : (6 : ℝ) ≤ n := by exact_mod_cast hn
  have hC : Cin (π * 6 / 2) ≤ Cin (π * n / 2) :=
    Cin_mono (by positivity) (by nlinarith [Real.pi_pos])
  have hb := modeE_tail_base ha ha1 hn
  have hc := cin_val6
  unfold tauF
  linarith

theorem dlo1 : (0.36338 : ℝ) ≤ 1 - 2 * Real.sin (π * ((1 : ℤ) : ℝ) / 2) / (π * ((1 : ℤ) : ℝ)) := by
  push_cast
  rw [show π * (1 : ℝ) / 2 = 2 * π / 4 by ring, (sc2).1]
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ := num_atoms
  have e : ∀ s : ℝ, 2 * s / (π * 1) = (2 * s / 1) * (1 / π) := fun s => by field_simp
  rw [e]
  nlinarith

theorem term1 {a : ℝ} (ha : 0 < a) (ha2 : a ≤ 0.3466) {g : ℝ → ℝ} (hp : Probe a g)
    (hn : normSq g = 1) (h0 : poleR g a = 0) :
    ((0.5408 : ℝ) + a * 0.36338 - errK a - tauF a) * 0.00306 ≤ (modeE a 1 - tauF a) * pm a g 1 := by
  have h := term_mode ha (by linarith) (k := 1) (by norm_num) (Cv := 0.5408) (D := 0.36338) (X := 0)
    (Y := 0) (τ := tauF a) (P := 0.00306) (by simpa using cin_val1) dlo1 le_rfl
    (by unfold tauF; linarith) (pm_le1 ha ha2 hp hn h0)
  linarith

theorem dlo2 : (1 : ℝ) ≤ 1 - 2 * Real.sin (π * ((2 : ℤ) : ℝ) / 2) / (π * ((2 : ℤ) : ℝ)) := by
  push_cast
  rw [show π * (2 : ℝ) / 2 = 4 * π / 4 by ring, (sc4).1]
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ := num_atoms
  have e : ∀ s : ℝ, 2 * s / (π * 2) = (2 * s / 2) * (1 / π) := fun s => by field_simp
  rw [e]
  nlinarith

theorem term2 {a : ℝ} (ha : 0 < a) (ha2 : a ≤ 0.3466) {g : ℝ → ℝ} (hp : Probe a g)
    (hn : normSq g = 1) (h0 : poleR g a = 0) :
    ((1.6214 : ℝ) + a * 1 - errK a - tauF a) * 0.02538 ≤ (modeE a 2 - tauF a) * pm a g 2 := by
  have h := term_mode ha (by linarith) (k := 2) (by norm_num) (Cv := 1.6214) (D := 1) (X := 0)
    (Y := 0) (τ := tauF a) (P := 0.02538) (by simpa using cin_val2) dlo2 le_rfl
    (by unfold tauF; linarith) (pm_le2 ha ha2 hp hn h0)
  linarith

theorem dlo3 : (1.212206 : ℝ) ≤ 1 - 2 * Real.sin (π * ((3 : ℤ) : ℝ) / 2) / (π * ((3 : ℤ) : ℝ)) := by
  push_cast
  rw [show π * (3 : ℝ) / 2 = 6 * π / 4 by ring, (sc6).1]
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ := num_atoms
  have e : ∀ s : ℝ, 2 * s / (π * 3) = (2 * s / 3) * (1 / π) := fun s => by field_simp
  rw [e]
  nlinarith

theorem term3 {a : ℝ} (ha : 0 < a) (ha2 : a ≤ 0.3466) {g : ℝ → ℝ} (hp : Probe a g)
    (hn : normSq g = 1) (h0 : poleR g a = 0) :
    ((2.2965 : ℝ) + a * 1.212206 - errK a - tauF a) * 0.07988 ≤ (modeE a 3 - tauF a) * pm a g 3 := by
  have h := term_mode ha (by linarith) (k := 3) (by norm_num) (Cv := 2.2965) (D := 1.212206) (X := 0)
    (Y := 0) (τ := tauF a) (P := 0.07988) (by simpa using cin_val3) dlo3 le_rfl
    (by unfold tauF; linarith) (pm_le3 ha ha2 hp hn h0)
  linarith

theorem dlo4 : (1 : ℝ) ≤ 1 - 2 * Real.sin (π * ((4 : ℤ) : ℝ) / 2) / (π * ((4 : ℤ) : ℝ)) := by
  push_cast
  rw [show π * (4 : ℝ) / 2 = 8 * π / 4 by ring, (sc8).1]
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ := num_atoms
  have e : ∀ s : ℝ, 2 * s / (π * 4) = (2 * s / 4) * (1 / π) := fun s => by field_simp
  rw [e]
  nlinarith

theorem term4 {a : ℝ} (ha : 0 < a) (ha2 : a ≤ 0.3466) {g : ℝ → ℝ} (hp : Probe a g)
    (hn : normSq g = 1) (h0 : poleR g a = 0) :
    ((2.4081 : ℝ) + a * 1 - errK a - tauF a) * 0.13125 ≤ (modeE a 4 - tauF a) * pm a g 4 := by
  have h := term_mode ha (by linarith) (k := 4) (by norm_num) (Cv := 2.4081) (D := 1) (X := 0)
    (Y := 0) (τ := tauF a) (P := 0.13125) (by simpa using cin_val4) dlo4 le_rfl
    (by unfold tauF; linarith) (pm_le4 ha ha2 hp hn h0)
  linarith

theorem dlo5 : (0.872676 : ℝ) ≤ 1 - 2 * Real.sin (π * ((5 : ℤ) : ℝ) / 2) / (π * ((5 : ℤ) : ℝ)) := by
  push_cast
  rw [show π * (5 : ℝ) / 2 = 10 * π / 4 by ring, (sc10).1]
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ := num_atoms
  have e : ∀ s : ℝ, 2 * s / (π * 5) = (2 * s / 5) * (1 / π) := fun s => by field_simp
  rw [e]
  nlinarith

theorem term5 {a : ℝ} (ha : 0 < a) (ha2 : a ≤ 0.3466) {g : ℝ → ℝ} (hp : Probe a g)
    (hn : normSq g = 1) (h0 : poleR g a = 0) :
    ((2.4848 : ℝ) + a * 0.872676 - errK a - tauF a) * 0.1395 ≤ (modeE a 5 - tauF a) * pm a g 5 := by
  have h := term_mode ha (by linarith) (k := 5) (by norm_num) (Cv := 2.4848) (D := 0.872676) (X := 0)
    (Y := 0) (τ := tauF a) (P := 0.1395) (by simpa using cin_val5) dlo5 le_rfl
    (by unfold tauF; linarith) (pm_le5 ha ha2 hp hn h0)
  linarith

/-- The low modes `−5, …, 5`. -/
def lowS : Finset ℤ := {-5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5}

theorem not_mem_lowS {n : ℤ} (hn : n ∉ lowS) : 6 ≤ n ∨ n ≤ -6 := by
  simp only [lowS, Finset.mem_insert, Finset.mem_singleton, not_or] at hn
  omega

/-- **A sum over `lowS` of an even function of the mode** is `f 0 + 2(f 1 + ⋯ + f 5)`. -/
theorem sum_lowS_even {f : ℤ → ℝ} (hf : ∀ k, f (-k) = f k) :
    ∑ n ∈ lowS, f n = f 0 + 2 * (f 1 + f 2 + f 3 + f 4 + f 5) := by
  simp only [lowS]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [show (-5 : ℤ) = -(5 : ℤ) from rfl, show (-4 : ℤ) = -(4 : ℤ) from rfl,
    show (-3 : ℤ) = -(3 : ℤ) from rfl, show (-2 : ℤ) = -(2 : ℤ) from rfl,
    show (-1 : ℤ) = -(1 : ℤ) from rfl, hf, hf, hf, hf, hf]
  ring

theorem tail_all {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (n : ℤ) (hn : n ∉ lowS) : tauF a ≤ modeE a n := by
  rcases not_mem_lowS hn with h | h
  · exact tail_ok ha ha1 h
  · have e := modeE_neg a (-n)
    rw [neg_neg] at e
    rw [e]; exact tail_ok ha ha1 (by omega)

/-- **The near-field energy of a normalised probe orthogonal to `w`, below the first prime.** -/
theorem nearField_fourier {a : ℝ} (ha : 0 < a) (ha2 : a ≤ 0.3466) {g : ℝ → ℝ} (hp : Probe a g)
    (hn : normSq g = 1) (h0 : poleR g a = 0) :
    tauF a - tauF a * (a ^ 4 / 240)
      + 2 * ((0.5408 + a * 0.36338 - errK a - tauF a) * 0.00306
        + (1.6214 + a * 1 - errK a - tauF a) * 0.02538
        + (2.2965 + a * 1.212206 - errK a - tauF a) * 0.07988
        + (2.4081 + a * 1 - errK a - tauF a) * 0.13125
        + (2.4848 + a * 0.872676 - errK a - tauF a) * 0.1395)
      ≤ ∫ u in Ioc 0 (2 * a), archIntegrand g u := by
  have hE := energy_ge_trunc ha hp hn lowS (tail_all ha (by linarith))
  have htau0 : 0 ≤ tauF a := by
    unfold tauF errK
    have : a ^ 2 ≤ 0.3466 * a := by nlinarith
    have : a ^ 3 ≤ 0.3466 ^ 2 * a := by nlinarith
    have : a ^ 4 ≤ 0.3466 ^ 3 * a := by nlinarith [pow_pos ha 3]
    have : a ^ 5 ≤ 0.3466 ^ 4 * a := by nlinarith [pow_pos ha 4]
    nlinarith
  have hsum : ∑ n ∈ lowS, (modeE a n - tauF a) * pm a g n
      = (modeE a 0 - tauF a) * pm a g 0
        + 2 * ((modeE a 1 - tauF a) * pm a g 1 + (modeE a 2 - tauF a) * pm a g 2
          + (modeE a 3 - tauF a) * pm a g 3 + (modeE a 4 - tauF a) * pm a g 4
          + (modeE a 5 - tauF a) * pm a g 5) :=
    sum_lowS_even fun k => by simp only [modeE_neg, pm_neg ha hp]
  rw [hsum] at hE
  have h0t : (0 - tauF a) * (a ^ 4 / 240) ≤ (modeE a 0 - tauF a) * pm a g 0 := by
    rw [modeE_zero]
    have := pm_zero_le ha (by linarith) hp hn h0
    nlinarith [pm_nonneg ha g 0]
  have t1 := term1 ha ha2 hp hn h0
  have t2 := term2 ha ha2 hp hn h0
  have t3 := term3 ha ha2 hp hn h0
  have t4 := term4 ha ha2 hp hn h0
  have t5 := term5 ha ha2 hp hn h0
  linarith

/-- **The gap below the first prime**: for `0 < a` with `2a < log 2`, every normalised probe `g`
with `ĝ(i/2) = 0` has `Q(g) ≥ Q(box) + 1/10`. -/
theorem weilQ_perp_ge_fourier {a : ℝ} (ha : 0 < a) (hlog : 2 * a < Real.log 2) {g : ℝ → ℝ}
    (hp : Probe a g) (hn : normSq g = 1) (h0 : poleR g a = 0) :
    weilQ a (box a) + 1 / 10 ≤ weilQ a g := by
  have hl2 := Real.log_two_lt_d9
  have ha2 : a ≤ 0.3466 := by norm_num at hl2; linarith
  have hQ : ∀ h, Probe a h → normSq h = 1 →
      weilQ a h = 2 * poleR h a ^ 2 + weilConst + archE h := by
    intro h hh hhn
    rw [weilQ_eq', primeS_eq_zero hlog hh, hhn]; ring
  rw [hQ g hp hn, hQ _ (box_probe a) (normSq_box ha), h0, archE_split ha hp hn,
    archE_split ha (box_probe a) (normSq_box ha)]
  have hG := nearField_fourier ha ha2 hp hn h0
  have hB := nearField_box_le' ha
  have hP := pole_box_le ha (by linarith)
  -- numerics
  have e1 : a ^ 2 ≤ 0.3466 * a := by nlinarith
  have e2 : a ^ 3 ≤ 0.3466 ^ 2 * a := by nlinarith
  have e3 : a ^ 4 ≤ 0.3466 ^ 3 * a := by nlinarith [pow_pos ha 3]
  have e4 : a ^ 5 ≤ 0.3466 ^ 4 * a := by nlinarith [pow_pos ha 4]
  have herr : errK a ≤ 0.2837 * a ^ 2 := by
    unfold errK; nlinarith [pow_pos ha 3, pow_pos ha 4, pow_pos ha 5]
  have herr0 : 0 ≤ errK a := by unfold errK; positivity
  have hpole : 4 * a * (1 + a ^ 2 / 24 + a ^ 4 / 1600) ^ 2 ≤ 4 * a + 0.34 * a ^ 3 := by
    have h8 : a ^ 8 ≤ 0.3466 ^ 6 * a ^ 2 := by nlinarith [pow_pos ha 2, pow_pos ha 6]
    have h6 : a ^ 6 ≤ 0.3466 ^ 4 * a ^ 2 := by nlinarith [pow_pos ha 2, pow_pos ha 4]
    nlinarith [pow_pos ha 3, pow_pos ha 5, pow_pos ha 7, pow_pos ha 9]
  have htau : tauF a ≤ 3.8 := by unfold tauF; nlinarith
  have htau0 : 0 ≤ tauF a := by unfold tauF; nlinarith
  have hsmall : tauF a * (a ^ 4 / 240) ≤ 3.8 * (0.3466 ^ 3 * a) / 240 := by
    have : 0 ≤ a ^ 4 := by positivity
    nlinarith
  unfold tauF at hG hsmall
  nlinarith

/-- **Certified lower bound orthogonally to `w`, for every `a` with `2a < log 2`**:
`Q₀(g) = Q(g) ≥ λ₁ + 1/10`. -/
theorem weilQ0_perp_ge_fourier {a : ℝ} (ha : 0 < a) (hlog : 2 * a < Real.log 2) {g : ℝ → ℝ}
    (hp : Probe a g) (hn : normSq g = 1) (h0 : poleR g a = 0) :
    lam a + 1 / 10 ≤ weilQ0 a g := by
  have hQ := weilQ_perp_ge_fourier ha hlog hp hn h0
  have hQ0 : weilQ0 a g = weilQ a g := by unfold weilQ0; rw [h0]; ring
  have hlam := lam_le (box_probe a) (normSq_box ha)
  rw [hQ0]; linarith

/-- **The ground state of `Q` is unique up to sign for every `a > 0` with `2a < log 2`.** -/
theorem groundState_unique_below_log2 {a : ℝ} (ha : 0 < a) (hlog : 2 * a < Real.log 2)
    {g h : ℝ → ℝ} (hg : IsGroundState a g) (hh : IsGroundState a h) :
    g =ᵐ[volume] h ∨ g =ᵐ[volume] fun t => -h t := by
  refine groundState_unique ha (fun v hv hv0 => ?_) hg hh
  have h1 := weilQ_perp_ge_fourier ha hlog hv.1 hv.2.1 hv0
  have h2 := hv.2.2 (box a) (box_probe a) (normSq_box ha)
  linarith

/-! ## H. Past the first prime: `log 2 ≤ 2a ≤ 0.7` -/

theorem log_three_gt : (0.72 : ℝ) < Real.log 3 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  have h1 : Real.exp 0.72 < Real.exp 1 := Real.exp_lt_exp.2 (by norm_num)
  have h2 := Real.exp_one_lt_d9
  linarith

/-- For `2a ≤ 0.72`, only `n = 2` contributes: `S(g) = (log 2/√2)·f(log 2)`. -/
theorem primeS_eq_two {a : ℝ} (ha : 2 * a ≤ 0.72) {g : ℝ → ℝ} (hg : Probe a g) :
    primeS g = Real.log 2 / Real.sqrt 2 * autocorr g (Real.log 2) := by
  unfold primeS
  rw [tsum_eq_single 2]
  · rw [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]; push_cast; ring
  · intro n hn
    rcases lt_or_ge n 2 with h | h
    · interval_cases n <;> simp
    · have h3 : 3 ≤ n := by omega
      have hl : Real.log 3 ≤ Real.log n := Real.log_le_log (by norm_num) (by exact_mod_cast h3)
      have := log_three_gt
      have hz : autocorr g (Real.log n) = 0 :=
        autocorr_eq_zero hg.supp (by rw [abs_of_pos (by linarith)]; linarith)
      simp [hz]

/-- `f(2a) = 0`. -/
theorem autocorr_two_a {a : ℝ} (ha : 0 < a) {g : ℝ → ℝ} (hp : Probe a g) : autocorr g (2 * a) = 0 := by
  unfold autocorr
  have : (fun t => g t * g (t + 2 * a)) =ᵐ[volume] 0 := by
    have hne : ∀ᵐ t ∂volume, t ≠ -a := by
      rw [ae_iff]; simp
    filter_upwards [hne] with t ht
    by_cases h1 : a < |t|
    · simp [hp.supp t h1]
    · have htl : -a < t := lt_of_le_of_ne (neg_le_of_abs_le (not_lt.1 h1)) (Ne.symm ht)
      have : a < |t + 2 * a| := by rw [abs_of_pos (by linarith)]; linarith
      simp [hp.supp _ this]
  rw [integral_congr_ae this]; simp

/-- `f(u) = Σ p_n cos(πnu/4a)` for `0 ≤ u ≤ 2a`. -/
theorem hasSum_autocorr {a : ℝ} (ha : 0 < a) {g : ℝ → ℝ} (hp : Probe a g) (hn : normSq g = 1)
    {u : ℝ} (hu0 : 0 ≤ u) (hu : u ≤ 2 * a) :
    HasSum (fun n : ℤ => pm a g n * Real.cos (π * n * u / (4 * a))) (autocorr g u) := by
  have h1 := hasSum_pm ha hp
  rw [hn] at h1
  have h2 := hasSum_one_sub_autocorr ha hp hn hu0 hu
  convert h1.sub h2 using 1
  · funext n; ring
  · ring

/-- The prime defect of mode `n`: `δ_n = |cos(πn u₀/4a) − cos(πn·2a/4a)|`. -/
def primeD (a u₀ : ℝ) (n : ℤ) : ℝ :=
  |Real.cos (π * n * u₀ / (4 * a)) - Real.cos (π * n * (2 * a) / (4 * a))|

theorem primeD_le_two (a u₀ : ℝ) (n : ℤ) : primeD a u₀ n ≤ 2 := by
  unfold primeD
  have := abs_sub (Real.cos (π * n * u₀ / (4 * a))) (Real.cos (π * n * (2 * a) / (4 * a)))
  have h1 := Real.abs_cos_le_one (π * n * u₀ / (4 * a))
  have h2 := Real.abs_cos_le_one (π * n * (2 * a) / (4 * a))
  linarith

theorem primeD_le {a u₀ : ℝ} (ha : 0 < a) (n : ℤ) :
    primeD a u₀ n ≤ π * |(n : ℝ)| * |2 * a - u₀| / (4 * a) := by
  unfold primeD
  refine (Real.abs_cos_sub_cos_le _ _).trans (le_of_eq ?_)
  rw [show π * n * u₀ / (4 * a) - π * n * (2 * a) / (4 * a) = -(π * n * (2 * a - u₀) / (4 * a)) by
    ring, abs_neg, abs_div, abs_mul, abs_mul, abs_of_pos Real.pi_pos,
    abs_of_pos (by linarith : (0 : ℝ) < 4 * a)]

theorem primeD_neg (a u₀ : ℝ) (n : ℤ) : primeD a u₀ (-n) = primeD a u₀ n := by
  unfold primeD; push_cast
  rw [show π * -(n : ℝ) * u₀ / (4 * a) = -(π * n * u₀ / (4 * a)) by ring,
    show π * -(n : ℝ) * (2 * a) / (4 * a) = -(π * n * (2 * a) / (4 * a)) by ring,
    Real.cos_neg, Real.cos_neg]

/-- **The truncated lower bound with the prime term.** -/
theorem energy_prime_trunc {a : ℝ} (ha : 0 < a) {g : ℝ → ℝ} (hp : Probe a g) (hn : normSq g = 1)
    {u₀ : ℝ} (hu0 : 0 ≤ u₀) (hu : u₀ ≤ 2 * a) {c : ℝ} (hc : 0 ≤ c) (S₀ : Finset ℤ) {τ : ℝ}
    (hτ : ∀ n, n ∉ S₀ → τ ≤ modeE a n - c * primeD a u₀ n) :
    τ + ∑ n ∈ S₀, (modeE a n - c * primeD a u₀ n - τ) * pm a g n
      ≤ (∫ u in Ioc 0 (2 * a), archIntegrand g u) - c * autocorr g u₀ := by
  have hP := hasSum_pm ha hp
  rw [hn] at hP
  -- `f(u₀) = Σ p_n (cos(ω u₀) − cos(ω 2a))`
  have hF : HasSum (fun n : ℤ => pm a g n * (Real.cos (π * n * u₀ / (4 * a))
      - Real.cos (π * n * (2 * a) / (4 * a)))) (autocorr g u₀) := by
    have := (hasSum_autocorr ha hp hn hu0 hu).sub
      (hasSum_autocorr ha hp hn (by linarith) le_rfl)
    rw [autocorr_two_a ha hp, sub_zero] at this
    convert this using 1; funext n; ring
  have hbound : ∀ S : Finset ℤ, autocorr g u₀
      ≤ ∑ n ∈ S, pm a g n * primeD a u₀ n + 2 * (1 - ∑ n ∈ S, pm a g n) := by
    intro S
    set G : ℤ → ℝ := fun n => 2 * pm a g n + if n ∈ S then pm a g n * primeD a u₀ n - 2 * pm a g n else 0
    have hG : HasSum G (2 * 1 + ∑ n ∈ S, (pm a g n * primeD a u₀ n - 2 * pm a g n)) := by
      refine (hP.mul_left 2).add ?_
      have : HasSum (fun n : ℤ => if n ∈ S then pm a g n * primeD a u₀ n - 2 * pm a g n else 0)
          (∑ n ∈ S, if n ∈ S then pm a g n * primeD a u₀ n - 2 * pm a g n else 0) :=
        hasSum_sum_of_ne_finset_zero (fun n hn => by simp [hn])
      convert this using 1
      refine Finset.sum_congr rfl fun n hn => by simp [hn]
    have hfg : ∀ n : ℤ, pm a g n * (Real.cos (π * n * u₀ / (4 * a))
        - Real.cos (π * n * (2 * a) / (4 * a))) ≤ G n := by
      intro n
      simp only [G]
      have hp0 := pm_nonneg ha g n
      have hd := le_abs_self (Real.cos (π * n * u₀ / (4 * a)) - Real.cos (π * n * (2 * a) / (4 * a)))
      have hd2 : Real.cos (π * n * u₀ / (4 * a)) - Real.cos (π * n * (2 * a) / (4 * a)) ≤ 2 := by
        linarith [Real.cos_le_one (π * n * u₀ / (4 * a)), Real.neg_one_le_cos (π * n * (2 * a) / (4 * a))]
      split_ifs with h
      · unfold primeD; nlinarith
      · nlinarith
    have hle := hasSum_le hfg hF hG
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at hle; linarith
  have hT : Tendsto (fun S : Finset ℤ => ∑ n ∈ S₀, (modeE a n - c * primeD a u₀ n - τ) * pm a g n
      + τ * ∑ n ∈ S, pm a g n - 2 * c * (1 - ∑ n ∈ S, pm a g n)) atTop
      (𝓝 (∑ n ∈ S₀, (modeE a n - c * primeD a u₀ n - τ) * pm a g n + τ * 1 - 2 * c * (1 - 1))) :=
    ((tendsto_const_nhds.add (hP.const_mul τ)).sub
      ((tendsto_const_nhds.sub hP).const_mul (2 * c)))
  rw [sub_self, mul_zero, sub_zero, mul_one, add_comm] at hT
  refine le_of_tendsto hT ?_
  filter_upwards [eventually_ge_atTop S₀] with S hS
  have hsplit := Finset.sum_sdiff hS (f := pm a g)
  have hsplit2 := Finset.sum_sdiff hS (f := fun n => pm a g n * (modeE a n - c * primeD a u₀ n))
  have htail : τ * ∑ n ∈ S \ S₀, pm a g n ≤ ∑ n ∈ S \ S₀, pm a g n * (modeE a n - c * primeD a u₀ n) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun n hn' => ?_
    rw [Finset.mem_sdiff] at hn'
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left (hτ n hn'.2) (pm_nonneg ha g n)
  have hlow : ∑ n ∈ S₀, (modeE a n - c * primeD a u₀ n - τ) * pm a g n
      = ∑ n ∈ S₀, pm a g n * (modeE a n - c * primeD a u₀ n) - τ * ∑ n ∈ S₀, pm a g n := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun n _ => by ring
  have hle := sum_modeE_le ha hp hn S
  have hb := hbound S
  have hsum : ∑ n ∈ S, pm a g n * (modeE a n - c * primeD a u₀ n)
      = ∑ n ∈ S, pm a g n * modeE a n - c * ∑ n ∈ S, pm a g n * primeD a u₀ n := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun n _ => by ring
  rw [← hsplit, mul_add] at *
  rw [← hsplit2] at hsum
  nlinarith

theorem primeD_nonneg (a u₀ : ℝ) (n : ℤ) : 0 ≤ primeD a u₀ n := abs_nonneg _

theorem primeD_small {a : ℝ} (hlo : Real.log 2 ≤ 2 * a) (ha2 : a ≤ 0.35) (n : ℤ) :
    primeD a (Real.log 2) n ≤ 0.01553 * |(n : ℝ)| := by
  have hl1 := Real.log_two_gt_d9
  have ha : (0.34657359 : ℝ) ≤ a := by linarith
  have ha0 : 0 < a := by linarith
  refine (primeD_le ha0 n).trans ?_
  rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ 2 * a - Real.log 2), div_le_iff₀ (by linarith)]
  have hπ := Real.pi_lt_d6
  have hn0 := abs_nonneg (n : ℝ)
  have hε : 2 * a - Real.log 2 ≤ 0.0068528197 := by linarith
  have hε0 : 0 ≤ 2 * a - Real.log 2 := by linarith
  have h1 : π * |(n : ℝ)| * (2 * a - Real.log 2) ≤ 3.141593 * |(n : ℝ)| * 0.0068528197 := by
    have := mul_le_mul (mul_le_mul_of_nonneg_right hπ.le hn0) hε hε0 (by positivity)
    linarith
  nlinarith

/-- **One tail branch**: for `6 ≤ n` with `M ≤ n` and `D_n ≤ B`, the `Cin` value at `Mπ/2` gives
`ψ_n − c·D_n ≥ C_v + a(1 − 0.31831/3) − err(a) − c·B`. -/
theorem tail_branch {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) {c : ℝ} (hc0 : 0 ≤ c) {n : ℤ} (hn : 6 ≤ n)
    {M Cv B : ℝ} (hM : 0 ≤ M) (hMn : M ≤ n) (hcv : Cv ≤ Cin (M * π / 2))
    (hD : primeD a (Real.log 2) n ≤ B) :
    Cv + a * (1 - 0.31831 / 3) - errK a - c * B ≤ modeE a n - c * primeD a (Real.log 2) n := by
  have hb := modeE_tail_base ha ha1 hn
  have hC : Cin (M * π / 2) ≤ Cin (π * n / 2) :=
    Cin_mono (by positivity) (by nlinarith [Real.pi_pos])
  linarith [mul_le_mul_of_nonneg_left hD hc0]

theorem tailB_pos {a : ℝ} (ha : 0 < a) (hlo : Real.log 2 ≤ 2 * a) (ha2 : a ≤ 0.35) {c : ℝ}
    (hc0 : 0 ≤ c) (hc : c ≤ 0.9803) {n : ℤ} (hn : 6 ≤ n) :
    2.8 ≤ modeE a n - c * primeD a (Real.log 2) n := by
  have hl1 := Real.log_two_gt_d9
  have ha' : (0.34657 : ℝ) ≤ a := by linarith
  have herr : errK a ≤ 0.0349 := by
    unfold errK
    have h2 : a ^ 2 ≤ 0.35 ^ 2 := pow_le_pow_left₀ ha.le ha2 2
    have h3 : a ^ 3 ≤ 0.35 ^ 3 := pow_le_pow_left₀ ha.le ha2 3
    have h4 : a ^ 4 ≤ 0.35 ^ 4 := pow_le_pow_left₀ ha.le ha2 4
    have h5 : a ^ 5 ≤ 0.35 ^ 5 := pow_le_pow_left₀ ha.le ha2 5
    norm_num at h2 h3 h4 h5 ⊢; linarith
  have hnr : (6 : ℝ) ≤ n := by exact_mod_cast hn
  have hD := primeD_small hlo ha2 n
  rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ n)] at hD
  have br := fun (M N Cv : ℝ) (hM : 0 ≤ M) (hMn : M ≤ n) (hnN : (n : ℝ) ≤ N)
      (hcv : Cv ≤ Cin (M * π / 2)) =>
    tail_branch ha (by linarith) hc0 hn hM hMn hcv
      (hD.trans (mul_le_mul_of_nonneg_left hnN (by norm_num : (0 : ℝ) ≤ 0.01553)))
  rcases le_or_gt n 10 with h | h
  · have := br 6 10 2.7801 (by norm_num) hnr (by exact_mod_cast h)
      (by rw [show (6 : ℝ) * π / 2 = π * 6 / 2 by ring]; exact cin_val6)
    linarith
  rcases le_or_gt n 20 with h | h
  · have := br 11 20 3.453456 (by norm_num) (by exact_mod_cast (show (11 : ℤ) ≤ n by omega))
      (by exact_mod_cast h) (by rw [show (11 : ℝ) * π / 2 = 22 * π / 4 by ring]; exact cinH11)
    linarith
  rcases le_or_gt n 60 with h | h
  · have := br 21 60 4.012087 (by norm_num) (by exact_mod_cast (show (21 : ℤ) ≤ n by omega))
      (by exact_mod_cast h) (by rw [show (21 : ℝ) * π / 2 = 42 * π / 4 by ring]; exact cinH21)
    linarith
  · have := tail_branch ha (by linarith) hc0 hn (M := 61) (Cv := 5.098076) (by norm_num)
      (by exact_mod_cast (show (61 : ℤ) ≤ n by omega))
      (by rw [show (61 : ℝ) * π / 2 = 122 * π / 4 by ring]; exact cinH61)
      (primeD_le_two a (Real.log 2) n)
    linarith

theorem tailB_all {a : ℝ} (ha : 0 < a) (hlo : Real.log 2 ≤ 2 * a) (ha2 : a ≤ 0.35) {c : ℝ}
    (hc0 : 0 ≤ c) (hc : c ≤ 0.9803) (n : ℤ) (hn : n ∉ lowS) :
    2.8 ≤ modeE a n - c * primeD a (Real.log 2) n := by
  rcases not_mem_lowS hn with h | h
  · exact tailB_pos ha hlo ha2 hc0 hc h
  · have e := modeE_neg a (-n)
    have e2 := primeD_neg a (Real.log 2) (-n)
    rw [neg_neg] at e e2
    rw [e, e2]; exact tailB_pos ha hlo ha2 hc0 hc (by omega)

theorem pm_leB1 {a : ℝ} (ha : 0 < a) (ha2 : a ≤ 0.35) {g : ℝ → ℝ} (hp : Probe a g)
    (hn : normSq g = 1) (h0 : poleR g a = 0) : pm a g 1 ≤ (0.0031 : ℝ) :=
  (pm_le_of ha ha2 (by norm_num) hp hn h0 (by norm_num) cval1).trans (by norm_num)

theorem termB1 {a : ℝ} (ha : 0 < a) (hlo : Real.log 2 ≤ 2 * a) (ha2 : a ≤ 0.35)
    {g : ℝ → ℝ} (hp : Probe a g) (hn : normSq g = 1) (h0 : poleR g a = 0) {c : ℝ} (hc0 : 0 ≤ c) :
    ((0.5408 : ℝ) + a * 0.36338 - errK a - c * (0.01553 * 1) - 2.8) * 0.0031
      ≤ (modeE a 1 - c * primeD a (Real.log 2) 1 - 2.8) * pm a g 1 := by
  have hD := primeD_small hlo ha2 1
  rw [show |(((1 : ℤ) : ℝ))| = 1 by norm_num] at hD
  have h := term_mode ha (by linarith) (k := 1) (by norm_num) (Cv := 0.5408) (D := 0.36338)
    (X := c * (0.01553 * 1)) (Y := c * primeD a (Real.log 2) 1) (τ := 2.8) (P := 0.0031)
    (by simpa using cin_val1) dlo1 (mul_le_mul_of_nonneg_left hD hc0)
    (by linarith [errK_nonneg ha.le, mul_nonneg hc0 (show (0 : ℝ) ≤ 0.01553 * 1 by norm_num)])
    (pm_leB1 ha ha2 hp hn h0)
  linarith

theorem pm_leB2 {a : ℝ} (ha : 0 < a) (ha2 : a ≤ 0.35) {g : ℝ → ℝ} (hp : Probe a g)
    (hn : normSq g = 1) (h0 : poleR g a = 0) : pm a g 2 ≤ (0.0254 : ℝ) :=
  (pm_le_of ha ha2 (by norm_num) hp hn h0 (by norm_num) cval2).trans (by norm_num)

theorem termB2 {a : ℝ} (ha : 0 < a) (hlo : Real.log 2 ≤ 2 * a) (ha2 : a ≤ 0.35)
    {g : ℝ → ℝ} (hp : Probe a g) (hn : normSq g = 1) (h0 : poleR g a = 0) {c : ℝ} (hc0 : 0 ≤ c) :
    ((1.6214 : ℝ) + a * 1 - errK a - c * (0.01553 * 2) - 2.8) * 0.0254
      ≤ (modeE a 2 - c * primeD a (Real.log 2) 2 - 2.8) * pm a g 2 := by
  have hD := primeD_small hlo ha2 2
  rw [show |(((2 : ℤ) : ℝ))| = 2 by norm_num] at hD
  have h := term_mode ha (by linarith) (k := 2) (by norm_num) (Cv := 1.6214) (D := 1)
    (X := c * (0.01553 * 2)) (Y := c * primeD a (Real.log 2) 2) (τ := 2.8) (P := 0.0254)
    (by simpa using cin_val2) dlo2 (mul_le_mul_of_nonneg_left hD hc0)
    (by linarith [errK_nonneg ha.le, mul_nonneg hc0 (show (0 : ℝ) ≤ 0.01553 * 2 by norm_num)])
    (pm_leB2 ha ha2 hp hn h0)
  linarith

theorem pm_leB3 {a : ℝ} (ha : 0 < a) (ha2 : a ≤ 0.35) {g : ℝ → ℝ} (hp : Probe a g)
    (hn : normSq g = 1) (h0 : poleR g a = 0) : pm a g 3 ≤ (0.07988 : ℝ) :=
  (pm_le_of ha ha2 (by norm_num) hp hn h0 (by norm_num) cval3).trans (by norm_num)

theorem termB3 {a : ℝ} (ha : 0 < a) (hlo : Real.log 2 ≤ 2 * a) (ha2 : a ≤ 0.35)
    {g : ℝ → ℝ} (hp : Probe a g) (hn : normSq g = 1) (h0 : poleR g a = 0) {c : ℝ} (hc0 : 0 ≤ c) :
    ((2.2965 : ℝ) + a * 1.212206 - errK a - c * (0.01553 * 3) - 2.8) * 0.07988
      ≤ (modeE a 3 - c * primeD a (Real.log 2) 3 - 2.8) * pm a g 3 := by
  have hD := primeD_small hlo ha2 3
  rw [show |(((3 : ℤ) : ℝ))| = 3 by norm_num] at hD
  have h := term_mode ha (by linarith) (k := 3) (by norm_num) (Cv := 2.2965) (D := 1.212206)
    (X := c * (0.01553 * 3)) (Y := c * primeD a (Real.log 2) 3) (τ := 2.8) (P := 0.07988)
    (by simpa using cin_val3) dlo3 (mul_le_mul_of_nonneg_left hD hc0)
    (by linarith [errK_nonneg ha.le, mul_nonneg hc0 (show (0 : ℝ) ≤ 0.01553 * 3 by norm_num)])
    (pm_leB3 ha ha2 hp hn h0)
  linarith

theorem pm_leB4 {a : ℝ} (ha : 0 < a) (ha2 : a ≤ 0.35) {g : ℝ → ℝ} (hp : Probe a g)
    (hn : normSq g = 1) (h0 : poleR g a = 0) : pm a g 4 ≤ (0.13125 : ℝ) :=
  (pm_le_of ha ha2 (by norm_num) hp hn h0 (by norm_num) cval4).trans (by norm_num)

theorem termB4 {a : ℝ} (ha : 0 < a) (hlo : Real.log 2 ≤ 2 * a) (ha2 : a ≤ 0.35)
    {g : ℝ → ℝ} (hp : Probe a g) (hn : normSq g = 1) (h0 : poleR g a = 0) {c : ℝ} (hc0 : 0 ≤ c) :
    ((2.4081 : ℝ) + a * 1 - errK a - c * (0.01553 * 4) - 2.8) * 0.13125
      ≤ (modeE a 4 - c * primeD a (Real.log 2) 4 - 2.8) * pm a g 4 := by
  have hD := primeD_small hlo ha2 4
  rw [show |(((4 : ℤ) : ℝ))| = 4 by norm_num] at hD
  have h := term_mode ha (by linarith) (k := 4) (by norm_num) (Cv := 2.4081) (D := 1)
    (X := c * (0.01553 * 4)) (Y := c * primeD a (Real.log 2) 4) (τ := 2.8) (P := 0.13125)
    (by simpa using cin_val4) dlo4 (mul_le_mul_of_nonneg_left hD hc0)
    (by linarith [errK_nonneg ha.le, mul_nonneg hc0 (show (0 : ℝ) ≤ 0.01553 * 4 by norm_num)])
    (pm_leB4 ha ha2 hp hn h0)
  linarith

theorem pm_leB5 {a : ℝ} (ha : 0 < a) (ha2 : a ≤ 0.35) {g : ℝ → ℝ} (hp : Probe a g)
    (hn : normSq g = 1) (h0 : poleR g a = 0) : pm a g 5 ≤ (0.1395 : ℝ) :=
  (pm_le_of ha ha2 (by norm_num) hp hn h0 (by norm_num) cval5).trans (by norm_num)

theorem termB5 {a : ℝ} (ha : 0 < a) (hlo : Real.log 2 ≤ 2 * a) (ha2 : a ≤ 0.35)
    {g : ℝ → ℝ} (hp : Probe a g) (hn : normSq g = 1) (h0 : poleR g a = 0) {c : ℝ} (hc0 : 0 ≤ c) :
    ((2.4848 : ℝ) + a * 0.872676 - errK a - c * (0.01553 * 5) - 2.8) * 0.1395
      ≤ (modeE a 5 - c * primeD a (Real.log 2) 5 - 2.8) * pm a g 5 := by
  have hD := primeD_small hlo ha2 5
  rw [show |(((5 : ℤ) : ℝ))| = 5 by norm_num] at hD
  have h := term_mode ha (by linarith) (k := 5) (by norm_num) (Cv := 2.4848) (D := 0.872676)
    (X := c * (0.01553 * 5)) (Y := c * primeD a (Real.log 2) 5) (τ := 2.8) (P := 0.1395)
    (by simpa using cin_val5) dlo5 (mul_le_mul_of_nonneg_left hD hc0)
    (by linarith [errK_nonneg ha.le, mul_nonneg hc0 (show (0 : ℝ) ≤ 0.01553 * 5 by norm_num)])
    (pm_leB5 ha ha2 hp hn h0)
  linarith

theorem pole_poly_le {a : ℝ} (ha : 0 < a) (ha2 : a ≤ 0.35) :
    4 * a * (1 + a ^ 2 / 24 + a ^ 4 / 1600) ^ 2 ≤ 4 * a + 0.34 * a ^ 3 := by
  have h6p : a ^ 6 ≤ 0.35 ^ 6 := pow_le_pow_left₀ ha.le ha2 6
  have h4p : a ^ 4 ≤ 0.35 ^ 4 := pow_le_pow_left₀ ha.le ha2 4
  have h8 : a ^ 8 ≤ 0.35 ^ 6 * a ^ 2 := by nlinarith [pow_pos ha 2, pow_pos ha 6]
  have h6 : a ^ 6 ≤ 0.35 ^ 4 * a ^ 2 := by nlinarith [pow_pos ha 2, pow_pos ha 4]
  have e : 4 * a * (1 + a ^ 2 / 24 + a ^ 4 / 1600) ^ 2
      = 4 * a + a ^ 3 / 3 + a * (43 * a ^ 4 / 3600 + a ^ 6 / 4800 + a ^ 8 / 640000) := by ring
  rw [e]
  have : 43 * a ^ 4 / 3600 + a ^ 6 / 4800 + a ^ 8 / 640000 ≤ 0.0066 * a ^ 2 := by
    have h4 : a ^ 4 ≤ 0.35 ^ 2 * a ^ 2 := by nlinarith [pow_pos ha 2]
    norm_num at h4 h6 h8 ⊢; nlinarith [pow_pos ha 2]
  have h3 : a * (43 * a ^ 4 / 3600 + a ^ 6 / 4800 + a ^ 8 / 640000) ≤ a * (0.0066 * a ^ 2) :=
    mul_le_mul_of_nonneg_left this ha.le
  nlinarith

theorem autocorr_box_nonneg (a u : ℝ) : 0 ≤ autocorr (box a) u := by
  unfold autocorr
  refine integral_nonneg fun t => mul_nonneg ?_ ?_ <;>
  · rw [box_apply]; split_ifs <;> positivity

/-- **The gap past the first prime**: for `log 2 ≤ 2a ≤ 0.7`, every normalised probe `g` with
`ĝ(i/2) = 0` has `Q(g) ≥ Q(box) + 1/40`. -/
theorem weilQ_perp_ge_sliver {a : ℝ} (ha : 0 < a) (hlo : Real.log 2 ≤ 2 * a) (ha2 : a ≤ 0.35)
    {g : ℝ → ℝ} (hp : Probe a g) (hn : normSq g = 1) (h0 : poleR g a = 0) :
    weilQ a (box a) + 1 / 40 ≤ weilQ a g := by
  have hl1 := Real.log_two_gt_d9
  have hl2 := Real.log_two_lt_d9
  have ha' : (0.3465 : ℝ) ≤ a := by linarith
  set c := 2 * (Real.log 2 / Real.sqrt 2) with hcdef
  obtain ⟨-, -, hs1, hs2, -⟩ := num_atoms
  have hc0 : 0 ≤ c := by positivity
  have hc : c ≤ 0.9803 := by
    have e : c = Real.sqrt 2 * Real.log 2 := by
      rw [hcdef]; field_simp; rw [Real.sq_sqrt (by norm_num)]
    rw [e]; nlinarith
  have hQ : ∀ h, Probe a h → normSq h = 1 →
      weilQ a h = 2 * poleR h a ^ 2 + weilConst + archE h - c * autocorr h (Real.log 2) := by
    intro h hh hhn
    rw [weilQ_eq', primeS_eq_two (by linarith) hh, hhn, hcdef]; ring
  rw [hQ g hp hn, hQ _ (box_probe a) (normSq_box ha), h0, archE_split ha hp hn,
    archE_split ha (box_probe a) (normSq_box ha)]
  have hu0 : 0 ≤ Real.log 2 := by linarith
  have hE := energy_prime_trunc ha hp hn hu0 hlo hc0 lowS (tailB_all ha hlo ha2 hc0 hc)
  have hsum : ∑ n ∈ lowS, (modeE a n - c * primeD a (Real.log 2) n - 2.8) * pm a g n
      = (modeE a 0 - c * primeD a (Real.log 2) 0 - 2.8) * pm a g 0
        + 2 * ((modeE a 1 - c * primeD a (Real.log 2) 1 - 2.8) * pm a g 1
          + (modeE a 2 - c * primeD a (Real.log 2) 2 - 2.8) * pm a g 2
          + (modeE a 3 - c * primeD a (Real.log 2) 3 - 2.8) * pm a g 3
          + (modeE a 4 - c * primeD a (Real.log 2) 4 - 2.8) * pm a g 4
          + (modeE a 5 - c * primeD a (Real.log 2) 5 - 2.8) * pm a g 5) :=
    sum_lowS_even fun k => by simp only [modeE_neg, primeD_neg, pm_neg ha hp]
  rw [hsum] at hE
  have h0t : (0 - 0 - 2.8) * (a ^ 4 / 240)
      ≤ (modeE a 0 - c * primeD a (Real.log 2) 0 - 2.8) * pm a g 0 := by
    rw [modeE_zero, show primeD a (Real.log 2) 0 = 0 by simp [primeD]]
    have := pm_zero_le ha (by linarith) hp hn h0
    nlinarith [pm_nonneg ha g 0]
  have t1 := termB1 ha hlo ha2 hp hn h0 hc0
  have t2 := termB2 ha hlo ha2 hp hn h0 hc0
  have t3 := termB3 ha hlo ha2 hp hn h0 hc0
  have t4 := termB4 ha hlo ha2 hp hn h0 hc0
  have t5 := termB5 ha hlo ha2 hp hn h0 hc0
  have hB := nearField_box_le' ha
  have hP := pole_box_le ha (by linarith)
  have hfb := autocorr_box_nonneg a (Real.log 2)
  have hcf : 0 ≤ c * autocorr (box a) (Real.log 2) := mul_nonneg hc0 hfb
  have herr : errK a ≤ 0.0349 := by
    unfold errK
    have h2 : a ^ 2 ≤ 0.35 ^ 2 := pow_le_pow_left₀ ha.le ha2 2
    have h3 : a ^ 3 ≤ 0.35 ^ 3 := pow_le_pow_left₀ ha.le ha2 3
    have h4 : a ^ 4 ≤ 0.35 ^ 4 := pow_le_pow_left₀ ha.le ha2 4
    have h5 : a ^ 5 ≤ 0.35 ^ 5 := pow_le_pow_left₀ ha.le ha2 5
    norm_num at h2 h3 h4 h5 ⊢; linarith
  have ha4 : a ^ 4 ≤ 0.35 ^ 4 := pow_le_pow_left₀ ha.le ha2 4
  have hpole := pole_poly_le ha ha2
  have ha3 : a ^ 3 ≤ 0.35 ^ 3 := pow_le_pow_left₀ ha.le ha2 3
  linarith

/-- **Certified lower bound orthogonally to `w` for every `0 < a ≤ 0.35`**: `λ_⊥ ≥ λ₁ + 1/40`. -/
theorem weilQ0_perp_ge_035 {a : ℝ} (ha : 0 < a) (ha2 : a ≤ 0.35) {g : ℝ → ℝ} (hp : Probe a g)
    (hn : normSq g = 1) (h0 : poleR g a = 0) : lam a + 1 / 40 ≤ weilQ0 a g := by
  have hQ : weilQ a (box a) + 1 / 40 ≤ weilQ a g := by
    rcases lt_or_ge (2 * a) (Real.log 2) with h | h
    · have := weilQ_perp_ge_fourier ha h hp hn h0; linarith
    · exact weilQ_perp_ge_sliver ha h ha2 hp hn h0
  have hQ0 : weilQ0 a g = weilQ a g := by unfold weilQ0; rw [h0]; ring
  have hlam := lam_le (box_probe a) (normSq_box ha)
  rw [hQ0]; linarith

/-- **The ground state of `Q` is unique up to sign for every `0 < a ≤ 0.35`.** -/
theorem groundState_unique_035 {a : ℝ} (ha : 0 < a) (ha2 : a ≤ 0.35) {g h : ℝ → ℝ}
    (hg : IsGroundState a g) (hh : IsGroundState a h) :
    g =ᵐ[volume] h ∨ g =ᵐ[volume] fun t => -h t := by
  refine groundState_unique ha (fun v hv hv0 => ?_) hg hh
  have h1 := weilQ0_perp_ge_035 ha ha2 hv.1 hv.2.1 hv0
  have h3 : weilQ0 a v = weilQ a v := by unfold weilQ0; rw [hv0]; ring
  have h2 : weilQ a v = lam a := by
    have := ((isGroundState_iff ha).1 hv).1.2; rw [this, hv.2.1, mul_one]
  linarith

end Pilot1ca

#print axioms Pilot1ca.hasSum_one_sub_autocorr
#print axioms Pilot1ca.energy_ge_trunc
#print axioms Pilot1ca.kerK_ge_taylor
#print axioms Pilot1ca.modeE_ge
#print axioms Pilot1ca.cin_val6
#print axioms Pilot1ca.cin_chain
#print axioms Pilot1ca.pm_le_of
#print axioms Pilot1ca.term_mode
#print axioms Pilot1ca.tail_branch
#print axioms Pilot1ca.sum_lowS_even
#print axioms Pilot1ca.cinH61
#print axioms Pilot1ca.cs_supp
#print axioms Pilot1ca.integral_sq_perp
#print axioms Pilot1ca.pm_le
#print axioms Pilot1ca.nearField_fourier
#print axioms Pilot1ca.weilQ_perp_ge_fourier
#print axioms Pilot1ca.weilQ0_perp_ge_fourier
#print axioms Pilot1ca.groundState_unique_below_log2
#print axioms Pilot1ca.primeS_eq_two
#print axioms Pilot1ca.energy_prime_trunc
#print axioms Pilot1ca.tailB_all
#print axioms Pilot1ca.weilQ_perp_ge_sliver
#print axioms Pilot1ca.weilQ0_perp_ge_035
#print axioms Pilot1ca.groundState_unique_035
