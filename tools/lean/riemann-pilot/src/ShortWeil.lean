import Mathlib
import WeilZeta
import GroundState
import WeilDischarge
import KaiserZeroWeight
import ExplicitBridge
import PhiLadder

/-! # Primes in short intervals, part 1: the explicit formula side (round 235)

The test function is `h(z) = 2cos(Lz)·ĝ(z)²`, `L = log x`, where `g = g_J` is the `J`-th iterated
autocorrelation of the box `1_{[−b, b]}`. Then:
* `ĝ_J = ĝ_box^{2^J}` on all of `ℂ` (`ghatC_gI`), so `|ĝ_J(z)| ≤ (4b e^{b|Im z|}/(1 + b|z|))^{2^J}`
  decays to any fixed order;
* the prime side of Weil's formula is `2Σ Λ(n)n^{−1/2} g_{J+1}(log n − L)`, a nonnegative weight on
  `|log n − L| ≤ 2^{J+1}b` (`gh_hmod`);
* the pole terms give `4cosh(L/2)·ĝ_box(i/2)^{2^{J+1}} ≥ 2√x (2be^{−b/2})^{2^{J+1}}`.

`lower_bound` is the resulting inequality: the weighted prime sum near `x` is at least the pole term,
minus the zero sum weighted by `Wz`, minus an archimedean term of size `(4b)^k log(1/b)/b`.
-/

open Real Filter Topology Complex MeasureTheory Set

noncomputable section

namespace ShortWeil

open Pilot1ca Pilot1bt PilotWeil

/-! ## The probes -/

/-- The box `1_{[−b, b]}`. -/
def bx (b : ℝ) : ℝ → ℝ := Set.indicator (Icc (-b) b) fun _ => 1

theorem bx_apply (b u : ℝ) : bx b u = if |u| ≤ b then 1 else 0 := by
  unfold bx; simp [Set.indicator_apply, abs_le]

theorem bx_nonneg (b u : ℝ) : 0 ≤ bx b u := by rw [bx_apply]; split_ifs <;> norm_num

theorem esupp_bx (b : ℝ) : ESupp b (bx b) where
  even u := by rw [bx_apply, bx_apply, abs_neg]
  supp u hu := by rw [bx_apply]; simp [not_le.2 hu]
  memL2 := memLp_indicator_of_continuous continuous_const measurableSet_Icc measure_Icc_lt_top.ne
    (C := |(1 : ℝ)|) fun _ _ => le_rfl

/-- `g_0 = 1_{[−b,b]}`, `g_{j+1} = autocorr g_j`. -/
def gI (b : ℝ) : ℕ → ℝ → ℝ
  | 0 => bx b
  | j + 1 => autocorr (gI b j)

theorem autocorr_neg (g : ℝ → ℝ) (u : ℝ) : autocorr g (-u) = autocorr g u := by
  unfold autocorr
  have := integral_add_right_eq_self (μ := (volume : Measure ℝ)) (fun t => g t * g (t + -u)) u
  rw [← this]; congr 1; funext t; rw [show t + u + -u = t by ring, mul_comm]

theorem esupp_autocorr {a : ℝ} {g : ℝ → ℝ} (hp : ESupp a g) (_ha : 0 < a) :
    ESupp (2 * a) (autocorr g) where
  even u := autocorr_neg g u
  supp u hu := autocorr_eq_zero hp.supp hu
  memL2 := by
    refine (continuous_autocorr hp.memL2).memLp_of_hasCompactSupport ?_
    refine HasCompactSupport.intro (isCompact_Icc (a := -(2 * a)) (b := 2 * a)) fun u hu => ?_
    apply autocorr_eq_zero hp.supp
    by_contra h; push Not at h
    exact hu (abs_le.1 h)

theorem gI_esupp {b : ℝ} (hb : 0 < b) : ∀ j : ℕ, ESupp (2 ^ j * b) (gI b j)
  | 0 => by simpa [gI] using esupp_bx b
  | j + 1 => by
    have e : (2 : ℝ) ^ (j + 1) * b = 2 * (2 ^ j * b) := by ring
    rw [e]; exact esupp_autocorr (gI_esupp hb j) (by positivity)

theorem gI_nonneg (b : ℝ) : ∀ (j : ℕ) (u : ℝ), 0 ≤ gI b j u
  | 0, u => bx_nonneg b u
  | j + 1, u => integral_nonneg fun t => mul_nonneg (gI_nonneg b j t) (gI_nonneg b j (t + u))

/-! ## The transforms -/

/-- Two entire functions that agree on `ℝ` agree everywhere. -/
theorem eq_of_real {f g : ℂ → ℂ} (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (h : ∀ r : ℝ, f r = g r) (z : ℂ) : f z = g z := by
  have ht : Tendsto (fun n : ℕ => (((1 : ℝ) / (n + 1) : ℝ) : ℂ)) atTop (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => ?_⟩
    · have := (Complex.continuous_ofReal.tendsto 0).comp tendsto_one_div_add_atTop_nhds_zero_nat
      simpa [Function.comp_def] using this
    · simp only [mem_compl_iff, mem_singleton_iff, Complex.ofReal_eq_zero]; positivity
  have hfr : ∃ᶠ w in 𝓝[≠] (0 : ℂ), f w = g w :=
    ht.frequently (Frequently.of_forall fun n => h _)
  exact (hf.differentiableOn.analyticOnNhd isOpen_univ).eqOn_of_preconnected_of_frequently_eq
    (hg.differentiableOn.analyticOnNhd isOpen_univ) isPreconnected_univ (mem_univ 0) hfr (mem_univ z)

/-- **`\widehat{autocorr g} = ĝ²` on all of `ℂ`.** -/
theorem ghatC_autocorr {a : ℝ} {g : ℝ → ℝ} (hp : ESupp a g) (ha : 0 < a) (z : ℂ) :
    ghatC (autocorr g) (2 * a) z = ghatC g a z ^ 2 := by
  have hq := esupp_autocorr hp ha
  refine eq_of_real (f := ghatC (autocorr g) (2 * a)) (g := fun z => ghatC g a z ^ 2)
    (ghatC_differentiable hq.integrable.intervalIntegrable)
    ((ghatC_differentiable hp.integrable.intervalIntegrable).pow 2) (fun r => ?_) z
  rw [ghatC_eq_integral (by positivity) hq.supp]
  exact fourier_autocorr hp ha r

theorem ghatC_gI {b : ℝ} (hb : 0 < b) (z : ℂ) :
    ∀ j : ℕ, ghatC (gI b j) (2 ^ j * b) z = ghatC (bx b) b z ^ (2 ^ j)
  | 0 => by simp [gI]
  | j + 1 => by
    have e : (2 : ℝ) ^ (j + 1) * b = 2 * (2 ^ j * b) := by ring
    rw [e]
    change ghatC (autocorr (gI b j)) _ z = _
    rw [ghatC_autocorr (gI_esupp hb j) (by positivity), ghatC_gI hb z j, ← pow_mul, pow_succ]

theorem norm_cexp_I_mul_le {z : ℂ} {b u : ℝ} (hu : |u| ≤ b) :
    ‖Complex.exp (Complex.I * z * u)‖ ≤ Real.exp (b * |z.im|) := by
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.2
  have e : (Complex.I * z * (u : ℂ)).re = -(z.im * u) := by simp [Complex.mul_re, Complex.mul_im]
  rw [e]
  have h1 := neg_abs_le (z.im * u)
  have h2 : |z.im * u| ≤ b * |z.im| := by rw [abs_mul, mul_comm]; exact mul_le_mul_of_nonneg_right hu (abs_nonneg _)
  linarith

/-- `ĝ_box(z) = ∫_{−b}^{b} e^{izu} du`. -/
theorem ghatC_bx (b : ℝ) (hb : 0 ≤ b) (z : ℂ) :
    ghatC (bx b) b z = ∫ u in (-b)..b, Complex.exp (Complex.I * z * u) := by
  unfold ghatC
  refine intervalIntegral.integral_congr fun u hu => ?_
  rw [uIcc_of_le (by linarith)] at hu
  simp [bx_apply, abs_le.2 hu]

theorem norm_ghatC_bx_le (b : ℝ) (hb : 0 ≤ b) (z : ℂ) :
    ‖ghatC (bx b) b z‖ ≤ 2 * b * Real.exp (b * |z.im|) := by
  rw [ghatC_bx b hb]
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := -b) (b := b)
    (f := fun u : ℝ => Complex.exp (Complex.I * z * u)) (C := Real.exp (b * |z.im|))
    (fun u hu => by
      rw [uIoc_of_le (by linarith)] at hu
      exact norm_cexp_I_mul_le (abs_le.2 ⟨hu.1.le, hu.2⟩))
  have e2 : |b - -b| = 2 * b := by
    have : b - -b = 2 * b := by ring
    rw [this, abs_of_nonneg (by linarith)]
  rw [e2] at this
  linarith

theorem norm_mul_ghatC_bx_le (b : ℝ) (hb : 0 ≤ b) (z : ℂ) :
    ‖z‖ * ‖ghatC (bx b) b z‖ ≤ 2 * Real.exp (b * |z.im|) := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp only [norm_zero, zero_mul]; positivity
  have hc : Complex.I * z ≠ 0 := mul_ne_zero Complex.I_ne_zero hz
  rw [ghatC_bx b hb]
  have e : (fun u : ℝ => Complex.exp (Complex.I * z * u)) = fun u : ℝ => Complex.exp ((Complex.I * z) * u) :=
    rfl
  rw [e, integral_exp_mul_complex hc, norm_div, norm_mul, Complex.norm_I, one_mul,
    mul_div_cancel₀ _ (norm_ne_zero_iff.2 hz)]
  refine (norm_sub_le _ _).trans ?_
  have h1 := norm_cexp_I_mul_le (z := z) (u := b) (b := b) (by rw [abs_of_nonneg hb])
  have h2 := norm_cexp_I_mul_le (z := z) (u := -b) (b := b) (by rw [abs_neg, abs_of_nonneg hb])
  linarith

/-- **`|ĝ_box(z)| ≤ 4b e^{b|Im z|}/(1 + b|z|)`.** -/
theorem norm_ghatC_bx_le' (b : ℝ) (hb : 0 ≤ b) (z : ℂ) :
    ‖ghatC (bx b) b z‖ ≤ 4 * b * Real.exp (b * |z.im|) / (1 + b * ‖z‖) := by
  rw [le_div_iff₀ (by positivity)]
  have h1 := norm_ghatC_bx_le b hb z
  have h2 := norm_mul_ghatC_bx_le b hb z
  nlinarith [Real.exp_pos (b * |z.im|)]

/-- `ĝ_box(i/2) = ∫_{−b}^{b} e^{−u/2} du ≥ 2b e^{−b/2}`. -/
theorem poleR_bx_ge {b : ℝ} (hb : 0 ≤ b) : 2 * b * Real.exp (-(b / 2)) ≤ poleR (bx b) b := by
  unfold poleR
  have h : ∫ u in (-b)..b, bx b u * Real.exp (-(u / 2)) = ∫ u in (-b)..b, Real.exp (-(u / 2)) := by
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [uIcc_of_le (by linarith)] at hu
    simp [bx_apply, abs_le.2 hu]
  rw [h]
  have := intervalIntegral.integral_mono_on (a := -b) (b := b) (by linarith) (μ := volume)
    (f := fun _ => Real.exp (-(b / 2))) (g := fun u => Real.exp (-(u / 2)))
    intervalIntegrable_const ((by fun_prop : Continuous fun u : ℝ => Real.exp (-(u / 2))).intervalIntegrable _ _)
    (fun u hu => Real.exp_le_exp.2 (by linarith [hu.2]))
  simp only [intervalIntegral.integral_const, smul_eq_mul] at this
  linarith

theorem norm_ghatC_gI_le {b : ℝ} (hb : 0 < b) (J : ℕ) (z : ℂ) :
    ‖ghatC (gI b J) (2 ^ J * b) z‖ ≤ (4 * b * Real.exp (b * |z.im|) / (1 + b * ‖z‖)) ^ (2 ^ J) := by
  rw [ghatC_gI hb z J, norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_ghatC_bx_le' b hb.le z) _

/-! ## The test function `h(z) = 2cos(Lz)·ĝ_J(z)²` -/

def hmod (b : ℝ) (J : ℕ) (L : ℝ) (z : ℂ) : ℂ :=
  2 * Complex.cos (L * z) * ghatC (gI b J) (2 ^ J * b) z ^ 2

def hmodR (b : ℝ) (J : ℕ) (L r : ℝ) : ℝ := 2 * Real.cos (L * r) * hsq (gI b J) (2 ^ J * b) r

theorem hmod_real {b : ℝ} (hb : 0 < b) (J : ℕ) (L r : ℝ) : hmod b J L r = hmodR b J L r := by
  unfold hmod hmodR
  rw [ghatC_real (gI_esupp hb J) (by positivity) r, hsq]
  push_cast
  rfl

theorem hmod_even {b : ℝ} (hb : 0 < b) (J : ℕ) (L : ℝ) (z : ℂ) : hmod b J L (-z) = hmod b J L z := by
  unfold hmod
  rw [ghatC_even (gI_esupp hb J).even, mul_neg, Complex.cos_neg]

theorem striptest_hmod {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) (J : ℕ) {L : ℝ} (hL : 0 ≤ L) :
    StripTest (hmod b J L) (2 * Real.exp L * ((4 * b * Real.exp b) ^ (2 ^ (J + 1)) / b ^ 2)) := by
  have hE := gI_esupp hb J
  refine ⟨((by fun_prop : Differentiable ℂ fun z : ℂ => 2 * Complex.cos (L * z)).mul
    ((ghatC_differentiable hE.integrable.intervalIntegrable).pow 2)).differentiableOn, fun t ht => ?_⟩
  have him : |t.im| ≤ 1 := abs_le.2 ⟨ht.1, ht.2⟩
  set q := 1 + b * ‖t‖ with hq
  have hq1 : 1 ≤ q := by have := norm_nonneg t; nlinarith
  set B := (4 * b * Real.exp b) ^ (2 ^ (J + 1)) with hB
  have hg : ‖ghatC (gI b J) (2 ^ J * b) t‖ ≤ (4 * b * Real.exp b / q) ^ (2 ^ J) := by
    refine (norm_ghatC_gI_le hb J t).trans (pow_le_pow_left₀ (by positivity) ?_ _)
    gcongr
    nlinarith
  have hg2 : ‖ghatC (gI b J) (2 ^ J * b) t‖ ^ 2 ≤ B / q ^ (2 ^ (J + 1)) := by
    calc _ ≤ ((4 * b * Real.exp b / q) ^ (2 ^ J)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hg 2
      _ = _ := by rw [← pow_mul, div_pow, hB, pow_succ]
  have hre : b ^ 2 * (1 + t.re ^ 2) ≤ q ^ 2 := by
    have h1 : |t.re| ≤ ‖t‖ := Complex.abs_re_le_norm t
    have h2 : t.re ^ 2 ≤ ‖t‖ ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    have hb2 : b ^ 2 ≤ 1 := by nlinarith
    nlinarith [norm_nonneg t, sq_nonneg b, mul_nonneg hb.le (norm_nonneg t)]
  have hk : q ^ 2 ≤ q ^ (2 ^ (J + 1)) := pow_le_pow_right₀ hq1 (by
      have : 1 ≤ 2 ^ J := Nat.one_le_two_pow; rw [pow_succ]; omega)
  have hc := norm_two_cos_strip hL ht
  have hB0 : 0 ≤ B := by positivity
  have hpos : 0 < 1 + t.re ^ 2 := by positivity
  have hqk : 0 < q ^ (2 ^ (J + 1)) := by positivity
  have key : ‖ghatC (gI b J) (2 ^ J * b) t‖ ^ 2 * (1 + t.re ^ 2) ≤ B / b ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    calc ‖ghatC (gI b J) (2 ^ J * b) t‖ ^ 2 * (1 + t.re ^ 2) * b ^ 2
        = ‖ghatC (gI b J) (2 ^ J * b) t‖ ^ 2 * (b ^ 2 * (1 + t.re ^ 2)) := by ring
      _ ≤ B / q ^ (2 ^ (J + 1)) * q ^ (2 ^ (J + 1)) :=
          mul_le_mul hg2 (hre.trans hk) (by positivity) (by positivity)
      _ = B := div_mul_cancel₀ _ hqk.ne'
  unfold hmod
  rw [norm_mul, norm_pow, le_div_iff₀ hpos]
  calc ‖2 * Complex.cos (↑L * t)‖ * ‖ghatC (gI b J) (2 ^ J * b) t‖ ^ 2 * (1 + t.re ^ 2)
      = ‖2 * Complex.cos (↑L * t)‖ * (‖ghatC (gI b J) (2 ^ J * b) t‖ ^ 2 * (1 + t.re ^ 2)) := by ring
    _ ≤ 2 * Real.exp L * (B / b ^ 2) := mul_le_mul hc key (by positivity) (by positivity)

/-- The explicit formula for `h`, proved (`weilExplicit_zeta`). -/
theorem weil_hmod {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) (J : ℕ) {L : ℝ} (hL : 0 ≤ L) :
    WeilExplicit zetaZeroFamily (hmod b J L) (hmodR b J L) :=
  weilExplicit_zeta (striptest_hmod hb hb1 J hL) (hmod_even hb J L) (hmod_real hb J L)

/-- **The prime side**: `g_h(u) = g_{J+1}(u − L) + g_{J+1}(u + L)`. -/
theorem gh_hmodR {b : ℝ} (hb : 0 < b) (J : ℕ) (L u : ℝ) :
    gh (hmodR b J L) u = gI b (J + 1) (u - L) + gI b (J + 1) (u + L) := by
  have hE := gI_esupp hb J
  have ha : (0 : ℝ) < 2 ^ J * b := by positivity
  change _ = autocorr (gI b J) (u - L) + autocorr (gI b J) (u + L)
  rw [← gh_hsq hE ha, ← gh_hsq hE ha]
  unfold gh hmodR
  rw [← mul_add, ← integral_add (integrable_hsq_cos hE ha _) (integrable_hsq_cos hE ha _)]
  congr 2; funext r
  rw [show r * (u - L) = r * u - r * L by ring, show r * (u + L) = r * u + r * L by ring,
    Real.cos_sub, Real.cos_add, mul_comm L r]
  ring

/-! ## The pole term -/

theorem hmod_I_half {b : ℝ} (hb : 0 < b) (J : ℕ) (L : ℝ) :
    hmod b J L (I / 2) = ((2 * Real.cosh (L / 2) * poleR (bx b) b ^ (2 ^ (J + 1)) : ℝ) : ℂ) := by
  unfold hmod
  rw [ghatC_gI hb (I / 2) J, ghatC_I_div_two, show (L : ℂ) * (I / 2) = ((L / 2 : ℝ) : ℂ) * I by
    push_cast; ring, Complex.cos_mul_I, ← pow_mul, ← pow_succ]
  push_cast; ring

/-! ## The archimedean term -/

theorem abs_psiRe_le (r : ℝ) : |psiRe r| ≤ Real.log (1 + |r|) + (4 + |psiRe 0|) := by
  have hz : 1 / 4 ≤ (zB r).re := by rw [zB_re]
  have hup : psiRe r ≤ Real.log ‖zB r‖ + 4 := Kaiser.digamma_re_le hz
  have hn : ‖zB r‖ ≤ 1 + |r| := by
    unfold zB
    refine (norm_add_le _ _).trans ?_
    rw [norm_div, norm_div, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs]
    norm_num; linarith [abs_nonneg r]
  have hn0 : 0 < ‖zB r‖ := lt_of_lt_of_le (by norm_num) (hz.trans (Complex.re_le_norm _))
  have hlog : Real.log ‖zB r‖ ≤ Real.log (1 + |r|) := Real.log_le_log hn0 hn
  have hlog0 : 0 ≤ Real.log (1 + |r|) := Real.log_nonneg (by linarith [abs_nonneg r])
  have hlow := psiRe_ge r
  rw [abs_le]; constructor
  · linarith [neg_abs_le (psiRe 0)]
  · linarith [abs_nonneg (psiRe 0)]

theorem abs_arch_le {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) {J : ℕ} (hJ : 1 ≤ J) (L : ℝ) :
    |1 / (2 * π) * ∫ r, hmodR b J L r * psiRe r|
      ≤ (4 * b) ^ (2 ^ (J + 1)) * (Real.log (1 / b) + 5 + |psiRe 0|) / b := by
  set k := 2 ^ (J + 1) with hk
  set B := (4 * b) ^ k with hB
  set C1 := Real.log (1 / b) + 5 + |psiRe 0| with hC1
  have hE := gI_esupp hb J
  have hlb : 0 ≤ Real.log (1 / b) := Real.log_nonneg (by rw [le_div_iff₀ hb]; linarith)
  have hk4 : 4 ≤ k := by
    have : 2 ≤ 2 ^ J := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ J := Nat.pow_le_pow_right (by norm_num) hJ
    rw [hk, pow_succ]; omega
  have hpt : ∀ r : ℝ, ‖hmodR b J L r * psiRe r‖ ≤ 2 * B * C1 * (1 + (b * r) ^ 2)⁻¹ := by
    intro r
    set q := 1 + b * |r| with hq
    have hq1 : 1 ≤ q := by have := abs_nonneg r; nlinarith
    have hg : |gH (gI b J) (2 ^ J * b) r| ≤ (4 * b / q) ^ (2 ^ J) := by
      have h1 := norm_ghatC_gI_le hb J (r : ℂ)
      rw [ghatC_real hE (by positivity) r, Complex.norm_real, Real.norm_eq_abs] at h1
      simpa [Complex.norm_real, Real.norm_eq_abs] using h1
    have hsq_le : hsq (gI b J) (2 ^ J * b) r ≤ B / q ^ k := by
      unfold hsq
      rw [← sq_abs]
      calc |gH (gI b J) (2 ^ J * b) r| ^ 2 ≤ ((4 * b / q) ^ (2 ^ J)) ^ 2 :=
            pow_le_pow_left₀ (abs_nonneg _) hg 2
        _ = B / q ^ k := by rw [← pow_mul, div_pow, hB, hk, pow_succ]
    have hh : |hmodR b J L r| ≤ 2 * (B / q ^ k) := by
      unfold hmodR
      rw [abs_mul, abs_mul, abs_of_nonneg (hsq_nonneg r), abs_two]
      have := Real.abs_cos_le_one (L * r)
      have := hsq_nonneg (g := gI b J) (a := 2 ^ J * b) r
      nlinarith
    have hps : |psiRe r| ≤ C1 * q := by
      have h1 := abs_psiRe_le r
      have h2 : Real.log (1 + |r|) ≤ Real.log (1 / b) + Real.log q := by
        rw [← Real.log_mul (by positivity) (by positivity)]
        apply Real.log_le_log (by positivity)
        rw [one_div, inv_mul_eq_div, le_div_iff₀ hb, hq]; nlinarith [abs_nonneg r]
      have h3 : Real.log q ≤ q - 1 := Real.log_le_sub_one_of_pos (by linarith)
      nlinarith [abs_nonneg (psiRe 0)]
    have hqk : q ^ 3 ≤ q ^ k := pow_le_pow_right₀ hq1 (by omega)
    have hq2 : 1 + (b * r) ^ 2 ≤ q ^ 2 := by
      rw [hq, mul_pow, ← sq_abs r]; nlinarith [abs_nonneg r, hb.le]
    have hC1 : 0 ≤ C1 := by positivity
    have hB0 : 0 ≤ B := by positivity
    rw [Real.norm_eq_abs, abs_mul]
    calc |hmodR b J L r| * |psiRe r| ≤ 2 * (B / q ^ k) * (C1 * q) :=
          mul_le_mul hh hps (abs_nonneg _) (by positivity)
      _ = 2 * B * C1 * (q / q ^ k) := by ring
      _ ≤ 2 * B * C1 * (1 + (b * r) ^ 2)⁻¹ := by
          gcongr
          rw [div_le_iff₀ (by positivity), ← div_eq_inv_mul, le_div_iff₀ (by positivity)]
          calc q * (1 + (b * r) ^ 2) ≤ q * q ^ 2 := by gcongr
            _ = q ^ 3 := by ring
            _ ≤ q ^ k := hqk
  have hint : Integrable (fun r : ℝ => 2 * B * C1 * (1 + (b * r) ^ 2)⁻¹) :=
    ((integrable_inv_one_add_sq.comp_mul_left' hb.ne').const_mul _)
  have hI : ∫ r : ℝ, 2 * B * C1 * (1 + (b * r) ^ 2)⁻¹ = 2 * B * C1 * (π / b) := by
    rw [integral_const_mul]
    have := Measure.integral_comp_mul_left (fun y : ℝ => (1 + y ^ 2)⁻¹) b
    rw [this, integral_univ_inv_one_add_sq, abs_inv, abs_of_pos hb, smul_eq_mul, inv_mul_eq_div]
  have hle := norm_integral_le_of_norm_le hint (Eventually.of_forall hpt)
  rw [hI, Real.norm_eq_abs] at hle
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * π))]
  calc 1 / (2 * π) * |∫ r, hmodR b J L r * psiRe r| ≤ 1 / (2 * π) * (2 * B * C1 * (π / b)) :=
        mul_le_mul_of_nonneg_left hle (by positivity)
    _ = B * C1 / b := by field_simp

/-! ## The zero side -/

/-- The zero weight `x^{|β − ½| − ½}/(1 + b|γ|)^k`. -/
def Wz (x b : ℝ) (k : ℕ) (ρ : ℂ) : ℝ := x ^ (|ρ.re - 1 / 2| - 1 / 2) / (1 + b * |ρ.im|) ^ k

theorem Wz_nonneg {x b : ℝ} (hx : 0 < x) (hb : 0 ≤ b) (k : ℕ) (ρ : ℂ) : 0 ≤ Wz x b k ρ := by
  unfold Wz; positivity

theorem norm_hmod_zero_le {b : ℝ} (hb : 0 < b) (J : ℕ) {x : ℝ} (hx : 1 ≤ x) {ρ : ℂ}
    (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    ‖hmod b J (Real.log x) ((ρ - 1 / 2) / I)‖
      ≤ 2 * Real.sqrt x * (4 * b * Real.exp (b / 2)) ^ (2 ^ (J + 1)) * Wz x b (2 ^ (J + 1)) ρ := by
  have hx0 : 0 < x := by linarith
  set t := (ρ - 1 / 2) / I with ht
  have hre : t.re = ρ.im := by simp [ht, Complex.div_I]
  have him : t.im = -(ρ.re - 1 / 2) := by simp [ht, Complex.div_I]
  have habs : |t.im| ≤ 1 / 2 := by rw [him, abs_neg, abs_le]; constructor <;> linarith
  have hnorm : |ρ.im| ≤ ‖t‖ := by rw [← hre]; exact Complex.abs_re_le_norm t
  set q := 1 + b * |ρ.im| with hq
  have hq1 : 1 ≤ q := by have := abs_nonneg ρ.im; nlinarith
  have hg : ‖ghatC (gI b J) (2 ^ J * b) t‖ ≤ (4 * b * Real.exp (b / 2) / q) ^ (2 ^ J) := by
    refine (norm_ghatC_gI_le hb J t).trans (pow_le_pow_left₀ (by positivity) ?_ _)
    apply div_le_div₀ (by positivity) (by gcongr; nlinarith) (by positivity)
      (by rw [hq]; exact add_le_add_right (mul_le_mul_of_nonneg_left hnorm hb.le) 1)
  have hg2 : ‖ghatC (gI b J) (2 ^ J * b) t‖ ^ 2
      ≤ (4 * b * Real.exp (b / 2)) ^ (2 ^ (J + 1)) / q ^ (2 ^ (J + 1)) := by
    calc _ ≤ ((4 * b * Real.exp (b / 2) / q) ^ (2 ^ J)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hg 2
      _ = _ := by rw [← pow_mul, div_pow, pow_succ]
  have hc : ‖2 * Complex.cos (↑(Real.log x) * t)‖ ≤ 2 * x ^ |ρ.re - 1 / 2| := by
    refine (norm_two_cos_le _).trans (le_of_eq ?_)
    have e : ((Real.log x : ℂ) * t).im = Real.log x * t.im := by simp [Complex.mul_im]
    rw [e, Real.rpow_def_of_pos hx0, abs_mul, him, abs_neg, abs_of_nonneg (Real.log_nonneg hx)]
  have hx' : x ^ |ρ.re - 1 / 2| = Real.sqrt x * x ^ (|ρ.re - 1 / 2| - 1 / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hx0]; congr 1; ring
  unfold hmod
  rw [norm_mul, norm_pow]
  calc ‖2 * Complex.cos (↑(Real.log x) * t)‖ * ‖ghatC (gI b J) (2 ^ J * b) t‖ ^ 2
      ≤ (2 * x ^ |ρ.re - 1 / 2|) * ((4 * b * Real.exp (b / 2)) ^ (2 ^ (J + 1)) / q ^ (2 ^ (J + 1))) :=
        mul_le_mul hc hg2 (by positivity) (by positivity)
    _ = _ := by rw [hx', hq]; unfold Wz; ring

/-- **The explicit-formula lower bound.** With `L = log x`, `k = 2^{J+1}` and `g_{J+1}` supported in
`[−2^{J+1}b, 2^{J+1}b]`:
`2Σ Λ(n)n^{−1/2} g_{J+1}(log n − L) ≥ 2√x(2be^{−b/2})^k − 2√x(4be^{b/2})^k Σ_ρ W_ρ − (4b)^k C(b)/b`. -/
theorem lower_bound {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) {J : ℕ} (hJ : 1 ≤ J) {x : ℝ} (hx : 1 < x)
    (hL : 2 ^ (J + 1) * b < Real.log x)
    (hs : Summable fun i => Wz x b (2 ^ (J + 1)) (zetaZeroFamily i)) :
    2 * Real.sqrt x * (2 * b * Real.exp (-(b / 2))) ^ (2 ^ (J + 1))
        - 2 * Real.sqrt x * (4 * b * Real.exp (b / 2)) ^ (2 ^ (J + 1))
          * ∑' i, Wz x b (2 ^ (J + 1)) (zetaZeroFamily i)
        - (4 * b) ^ (2 ^ (J + 1)) * (Real.log (1 / b) + 5 + |psiRe 0|) / b
      ≤ 2 * ∑' n : ℕ, ArithmeticFunction.vonMangoldt n / Real.sqrt n
          * gI b (J + 1) (Real.log n - Real.log x) := by
  set L := Real.log x with hLdef
  have hL0 : 0 ≤ L := Real.log_nonneg hx.le
  have hx0 : 0 < x := by linarith
  obtain ⟨-, hS⟩ := weil_hmod hb hb1 J hL0
  have hE1 := gI_esupp hb (J + 1)
  have eP : ∀ n : ℕ, gh (hmodR b J L) (Real.log n) = gI b (J + 1) (Real.log n - L) := by
    intro n
    have hn := Real.log_natCast_nonneg n
    rw [gh_hmodR hb J L, hE1.supp (Real.log n + L) (by rw [abs_of_nonneg (by linarith)]; linarith),
      add_zero]
  have e0 : gh (hmodR b J L) 0 = 0 := by
    rw [gh_hmodR hb J L, hE1.supp (0 - L) (by rw [zero_sub, abs_neg, abs_of_nonneg hL0]; exact hL),
      hE1.supp (0 + L) (by rw [zero_add, abs_of_nonneg hL0]; exact hL), add_zero]
  simp_rw [eP, e0] at hS
  rw [hmod_even hb J L, hmod_I_half hb J L] at hS
  set E := 1 / (2 * π) * ∫ r, hmodR b J L r * psiRe r with hEdef
  set P := ∑' n : ℕ, ArithmeticFunction.vonMangoldt n / Real.sqrt n * gI b (J + 1) (Real.log n - L)
    with hPdef
  set k := 2 ^ (J + 1) with hk
  set M := 2 * Real.cosh (L / 2) * poleR (bx b) b ^ k with hM
  set c := 2 * Real.sqrt x * (4 * b * Real.exp (b / 2)) ^ k with hc
  have hf : ∀ i, ‖hmod b J L ((zetaZeroFamily i - 1 / 2) / I)‖ ≤ c * Wz x b k (zetaZeroFamily i) :=
    fun i => by
      have hz : IsNontrivialZero (zetaZeroFamily i) := i.1.2
      exact norm_hmod_zero_le hb J hx.le hz.mem_strip.1 hz.mem_strip.2
  have hsn : Summable fun i => ‖hmod b J L ((zetaZeroFamily i - 1 / 2) / I)‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hf (hs.mul_left c)
  have hZ := (norm_tsum_le_tsum_norm hsn).trans
    ((hsn.tsum_le_tsum hf (hs.mul_left c)).trans (le_of_eq tsum_mul_left))
  rw [hS.tsum_eq] at hZ
  have hre := (Complex.re_le_norm _).trans hZ
  simp only [Complex.add_re, Complex.ofReal_re] at hre
  have hEb := abs_arch_le hb hb1 hJ L
  have hsq : Real.sqrt x = Real.exp (L / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx0, ← hLdef]; ring_nf
  have hp := poleR_bx_ge hb.le
  have hpk : (2 * b * Real.exp (-(b / 2))) ^ k ≤ poleR (bx b) b ^ k :=
    pow_le_pow_left₀ (by positivity) hp k
  have hcosh : Real.exp (L / 2) ≤ 2 * Real.cosh (L / 2) := by
    rw [Real.cosh_eq]; linarith [Real.exp_pos (-(L / 2))]
  have hMl : 2 * Real.sqrt x * (2 * b * Real.exp (-(b / 2))) ^ k ≤ 2 * M := by
    rw [hsq, hM]
    have h0 : 0 ≤ (2 * b * Real.exp (-(b / 2))) ^ k := by positivity
    nlinarith [Real.exp_pos (L / 2)]
  have := abs_le.1 hEb
  linarith

end ShortWeil

#print axioms ShortWeil.ghatC_gI
#print axioms ShortWeil.norm_ghatC_bx_le'
#print axioms ShortWeil.lower_bound
