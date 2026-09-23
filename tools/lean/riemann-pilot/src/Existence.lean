import Mathlib
import GroundState

/-! # Existence of the ground state, stage 1: the energy controls the Fourier tails

For a probe `g` at half-support `a > 0`, expand `g` in the Fourier series of `[−2a, 2a]` (period
`4a`), `c_n = (4a)⁻¹∫ e^{−2πint/4a} g(t) dt`. A shift by `|s| < a` keeps `g(· + s)` inside the period
and multiplies `c_n` by a phase, so Parseval gives

`‖g − g(· + s)‖² = 4a Σ_n |c_n|² (2 − 2cos(2πns/4a))`,

and `‖g − g(· + s)‖² = 2(f(0) − f(s))` is exactly the archimedean integrand's numerator.
-/

open Real Filter Topology Complex MeasureTheory Set

noncomputable section

namespace Pilot1ca

/-! ## The shift distance -/

theorem integrable_mul_shift {g : ℝ → ℝ} (hg : MemLp g 2 volume) (s : ℝ) :
    Integrable (fun t => g t * g (t + s)) := by
  have hI : Integrable (fun t => g t ^ 2) := hg.integrable_sq
  have hJ : Integrable (fun t => g (t + s) ^ 2) := hI.comp_add_right s
  have hm : AEStronglyMeasurable (fun t => g t * g (t + s)) volume :=
    hg.aestronglyMeasurable.mul
      (hg.aestronglyMeasurable.comp_measurePreserving (measurePreserving_add_right volume s))
  refine ((hI.add hJ).div_const 2).mono' hm (Eventually.of_forall fun t => ?_)
  show ‖g t * g (t + s)‖ ≤ (g t ^ 2 + g (t + s) ^ 2) / 2
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> nlinarith [sq_nonneg (g t - g (t + s)), sq_nonneg (g t + g (t + s))]

/-- **`‖g − g(· + s)‖² = 2(f(0) − f(s))`**. -/
theorem normSq_sub_shift {g : ℝ → ℝ} (hg : MemLp g 2 volume) (s : ℝ) :
    normSq (fun t => g t - g (t + s)) = 2 * (autocorr g 0 - autocorr g s) := by
  have hI : Integrable (fun t => g t ^ 2) := hg.integrable_sq
  have hJ : Integrable (fun t => g (t + s) ^ 2) := hI.comp_add_right s
  have hP := integrable_mul_shift hg s
  have hIJ : Integrable (fun t => g t ^ 2 + g (t + s) ^ 2) := hI.add hJ
  have hP2 : Integrable (fun t => 2 * (g t * g (t + s))) := hP.const_mul 2
  have e : (fun t => (g t - g (t + s)) ^ 2)
      = fun t => (g t ^ 2 + g (t + s) ^ 2) - 2 * (g t * g (t + s)) := by
    funext t; ring
  rw [autocorr_zero]
  unfold normSq autocorr
  rw [e, integral_sub hIJ hP2, integral_add hI hJ, integral_const_mul,
    integral_add_right_eq_self (fun t => g t ^ 2) s]
  ring

/-! ## Fourier coefficients on `[−2a, 2a]` -/

/-- `c_n(g) = (4a)⁻¹ ∫_{−2a}^{2a} e^{−2πint/4a} g(t) dt`. -/
def cf (a : ℝ) (g : ℝ → ℝ) (n : ℤ) : ℂ :=
  (1 / (4 * a) : ℂ) *
    ∫ t in (-(2 * a))..(2 * a), Complex.exp (-(2 * π * I * n * t / (4 * a))) * ((g t : ℝ) : ℂ)

theorem fourierCoeffOn_eq_cf {a : ℝ} (ha : 0 < a) (g : ℝ → ℝ) (n : ℤ) :
    fourierCoeffOn (show -(2 * a) < 2 * a by linarith) (fun t => ((g t : ℝ) : ℂ)) n
      = cf a g n := by
  rw [fourierCoeffOn_eq_integral]
  unfold cf
  simp only [fourier_coe_apply, smul_eq_mul, Complex.real_smul]
  have hT : (2 * a - -(2 * a) : ℝ) = 4 * a := by ring
  rw [hT]
  push_cast
  congr 1
  apply intervalIntegral.integral_congr
  intro t _
  simp only
  congr 2
  ring

theorem memLp_intervalIntegrable {g : ℝ → ℝ} (hg : MemLp g 2 volume) (α β : ℝ) :
    IntervalIntegrable g volume α β := by
  have h2 : MemLp g 2 (volume.restrict (Set.uIoc α β)) := hg.restrict _
  have : IsFiniteMeasure (volume.restrict (Set.uIoc α β)) :=
    isFiniteMeasure_restrict.2 (by simp [Set.uIoc])
  exact (intervalIntegrable_iff).2 (h2.integrable (by norm_num))

/-- Functions vanishing outside `[−r, r]`: the integral over any interval containing it. -/
theorem integral_eq_of_supp {f : ℝ → ℂ} {r α β : ℝ} (hsupp : ∀ u, r < |u| → f u = 0)
    (hα : α < -r) (hβ : r < β) : (∫ x in α..β, f x) = ∫ x, f x := by
  apply intervalIntegral.integral_eq_integral_of_support_subset
  intro u hu
  rw [Function.mem_support] at hu
  have : |u| ≤ r := by
    by_contra h'
    exact hu (hsupp u (lt_of_not_ge h'))
  exact ⟨by linarith [neg_abs_le u], by linarith [le_abs_self u]⟩

/-- **Parseval** on `[−2a, 2a]`, for `g` vanishing outside `[−r, r]`, `r < 2a`. -/
theorem hasSum_cf_sq {a r : ℝ} (ha : 0 < a) (hr : r < 2 * a) {g : ℝ → ℝ}
    (hg : MemLp g 2 volume) (hsupp : ∀ u, r < |u| → g u = 0) :
    HasSum (fun n => ‖cf a g n‖ ^ 2) ((4 * a)⁻¹ * normSq g) := by
  have hab : -(2 * a) < 2 * a := by linarith
  have hL2 : MemLp (fun t => ((g t : ℝ) : ℂ)) 2 (volume.restrict (Ioc (-(2 * a)) (2 * a))) :=
    (hg.ofReal).restrict _
  have h := hasSum_sq_fourierCoeffOn hab hL2
  simp only [fourierCoeffOn_eq_cf ha] at h
  convert h using 1
  rw [smul_eq_mul, show (2 * a - -(2 * a) : ℝ) = 4 * a by ring]
  congr 1
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  unfold normSq
  have hs2 : ∀ u, r < |u| → g u ^ 2 = 0 := fun u hu => by rw [hsupp u hu]; ring
  have key : (((∫ x in (-(2 * a))..(2 * a), g x ^ 2) : ℝ) : ℂ) = (((∫ x, g x ^ 2) : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_ofReal, ← integral_complex_ofReal]
    exact integral_eq_of_supp (f := fun u => ((g u ^ 2 : ℝ) : ℂ)) (r := r)
      (fun u hu => by rw [hs2 u hu]; simp) (by linarith) (by linarith)
  exact_mod_cast key.symm

/-- **A shift multiplies the coefficients by a phase**, for `g` vanishing outside `[−a, a]` and
`|s| < a`. -/
theorem cf_shift {a : ℝ} (ha : 0 < a) {g : ℝ → ℝ} (hsupp : ∀ u, a < |u| → g u = 0) {s : ℝ}
    (hs : |s| < a) (n : ℤ) :
    cf a (fun t => g (t + s)) n = Complex.exp (2 * π * I * n * s / (4 * a)) * cf a g n := by
  unfold cf
  set E : ℝ → ℂ := fun t => Complex.exp (-(2 * π * I * n * t / (4 * a))) with hE
  show (1 / (4 * a) : ℂ) * (∫ t in (-(2 * a))..(2 * a), E t * ((g (t + s) : ℝ) : ℂ))
    = Complex.exp (2 * π * I * n * s / (4 * a))
      * ((1 / (4 * a) : ℂ) * ∫ t in (-(2 * a))..(2 * a), E t * ((g t : ℝ) : ℂ))
  have h1 : (∫ t in (-(2 * a))..(2 * a), E t * ((g (t + s) : ℝ) : ℂ))
      = ∫ x in (-(2 * a) + s)..(2 * a + s), E (x - s) * ((g x : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_comp_add_right (fun x => E (x - s) * ((g x : ℝ) : ℂ)) s]
    simp only [add_sub_cancel_right]
  have hEs : ∀ x, E (x - s) = Complex.exp (2 * π * I * n * s / (4 * a)) * E x := by
    intro x; simp only [hE]; rw [← Complex.exp_add]; congr 1; push_cast; ring
  have hsuppC : ∀ u, a < |u| → E u * ((g u : ℝ) : ℂ) = 0 := fun u hu => by
    rw [hsupp u hu]; simp
  have hs1 := le_abs_self s
  have hs2 := neg_abs_le s
  rw [h1]
  simp_rw [hEs, mul_assoc]
  rw [intervalIntegral.integral_const_mul,
    integral_eq_of_supp hsuppC (by linarith) (by linarith),
    integral_eq_of_supp hsuppC (by linarith) (by linarith)]
  ring

theorem cf_sub {a : ℝ} {g₁ g₂ : ℝ → ℝ} (h₁ : IntervalIntegrable g₁ volume (-(2 * a)) (2 * a))
    (h₂ : IntervalIntegrable g₂ volume (-(2 * a)) (2 * a)) (n : ℤ) :
    cf a (fun t => g₁ t - g₂ t) n = cf a g₁ n - cf a g₂ n := by
  have hE : ContinuousOn (fun t : ℝ => Complex.exp (-(2 * π * I * n * t / (4 * a))))
      (Set.uIcc (-(2 * a)) (2 * a)) := by fun_prop
  have i₁ : IntervalIntegrable (fun t => Complex.exp (-(2 * π * I * n * t / (4 * a)))
      * ((g₁ t : ℝ) : ℂ)) volume (-(2 * a)) (2 * a) :=
    (show IntervalIntegrable (fun t => ((g₁ t : ℝ) : ℂ)) volume (-(2 * a)) (2 * a) from
      ⟨h₁.1.ofReal, h₁.2.ofReal⟩).continuousOn_mul hE
  have i₂ : IntervalIntegrable (fun t => Complex.exp (-(2 * π * I * n * t / (4 * a)))
      * ((g₂ t : ℝ) : ℂ)) volume (-(2 * a)) (2 * a) :=
    (show IntervalIntegrable (fun t => ((g₂ t : ℝ) : ℂ)) volume (-(2 * a)) (2 * a) from
      ⟨h₂.1.ofReal, h₂.2.ofReal⟩).continuousOn_mul hE
  unfold cf
  rw [← mul_sub, ← intervalIntegral.integral_sub i₁ i₂]
  congr 1
  apply intervalIntegral.integral_congr
  intro t _
  simp only
  push_cast
  ring

theorem norm_one_sub_exp_sq (θ : ℝ) : ‖1 - Complex.exp (θ * I)‖ ^ 2 = 2 - 2 * Real.cos θ := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.one_re, Complex.exp_ofReal_mul_I_re, Complex.sub_im,
    Complex.one_im, Complex.exp_ofReal_mul_I_im]
  linear_combination Real.sin_sq_add_cos_sq θ

/-- **Parseval for `g − g(· + s)`**: `Σ|c_n|²(2 − 2cos(2πns/4a)) = (4a)⁻¹·2(f(0) − f(s))`. -/
theorem hasSum_shift {a : ℝ} (ha : 0 < a) {g : ℝ → ℝ} (hp : Probe a g) {s : ℝ} (hs : |s| < a) :
    HasSum (fun n : ℤ => ‖cf a g n‖ ^ 2 * (2 - 2 * Real.cos (2 * π * n * s / (4 * a))))
      ((4 * a)⁻¹ * (2 * (autocorr g 0 - autocorr g s))) := by
  have hgs : MemLp (fun t => g (t + s)) 2 volume :=
    hp.memL2.comp_measurePreserving (measurePreserving_add_right volume s)
  have hmem : MemLp (fun t => g t - g (t + s)) 2 volume := hp.memL2.sub hgs
  have hsupp : ∀ u, a + |s| < |u| → g u - g (u + s) = 0 := by
    intro u hu
    have h1 : a < |u| := by linarith [abs_nonneg s]
    have h2 : a < |u + s| := by
      have : |u| ≤ |u + s| + |s| := by
        have := abs_sub (u + s) s
        rwa [add_sub_cancel_right] at this
      linarith
    rw [hp.supp u h1, hp.supp _ h2, sub_self]
  have hP := hasSum_cf_sq ha (by linarith) hmem hsupp
  rw [normSq_sub_shift hp.memL2 s] at hP
  convert hP using 1
  funext n
  have hlin : cf a (fun t => g t - g (t + s)) n
      = cf a g n * (1 - Complex.exp (((2 * π * n * s / (4 * a) : ℝ) : ℂ) * I)) := by
    rw [cf_sub (memLp_intervalIntegrable hp.memL2 _ _) (memLp_intervalIntegrable hgs _ _),
      cf_shift ha hp.supp hs n]
    have : Complex.exp (2 * π * I * n * s / (4 * a))
        = Complex.exp (((2 * π * n * s / (4 * a) : ℝ) : ℂ) * I) := by
      congr 1; push_cast; ring
    rw [this]; ring
  rw [hlin, norm_mul, mul_pow, norm_one_sub_exp_sq]

/-! ## The archimedean kernel near `0` -/

/-- **`e^{s/2}/sinh s ≥ 1/(2s)` on `(0, 1]`**: `sinh s ≤ s·e^s` and `e^{s/2} ≤ 2`. -/
theorem archK_ge {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    1 / (2 * s) ≤ Real.exp (s / 2) / Real.sinh s := by
  have hsh : 0 < Real.sinh s := Real.sinh_pos_iff.2 hs
  rw [div_le_div_iff₀ (by positivity) hsh, one_mul]
  set x := Real.exp (s / 2) with hx
  have hx0 : 0 < x := Real.exp_pos _
  have hA : Real.exp s = x ^ 2 := by rw [hx, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hB : Real.exp (-s) * Real.exp s = 1 := by rw [← Real.exp_add]; simp
  have hB2 : 1 - 2 * s ≤ Real.exp (-s) ^ 2 := by
    rw [← Real.exp_nat_mul]; push_cast
    rw [show (2 : ℝ) * -s = -2 * s by ring]
    linarith [Real.add_one_le_exp (-2 * s)]
  have hx2 : x ≤ 2 := by
    have h1 : x ≤ Real.exp (1 / 2) := Real.exp_le_exp.2 (by linarith)
    have h2 : Real.exp (1 / 2) ^ 2 < 2 ^ 2 := by
      rw [← Real.exp_nat_mul]; norm_num
      have := Real.exp_one_lt_d9; linarith
    nlinarith [Real.exp_pos (1 / 2)]
  have hBpos : 0 < Real.exp (-s) := Real.exp_pos _
  rw [Real.sinh_eq]
  -- `(e^s − e^{−s})/2 ≤ s·e^s ≤ 2s·x`
  have h1 : Real.exp s - Real.exp (-s) ≤ 2 * s * Real.exp s := by
    have : Real.exp s - Real.exp (-s) = Real.exp s * (1 - Real.exp (-s) ^ 2) := by
      have := hB; nlinarith
    rw [this]
    have := Real.exp_pos s
    nlinarith
  rw [hA] at h1 ⊢
  have h2 : s * x * x ≤ s * x * 2 := mul_le_mul_of_nonneg_left hx2 (by positivity)
  nlinarith

/-! ## The frequency weight `J(k) = ∫₀^b (2 − 2cos ks)/s ds ≥ 2 log(kb) − 6` -/

/-- `|∫_{1/k}^b cos(ks)/s ds| ≤ 3`, by parts. -/
theorem abs_integral_cos_div_le {b k : ℝ} (hk : 0 < k) (hkb : 1 ≤ k * b) :
    |∫ s in (1 / k)..b, Real.cos (k * s) / s| ≤ 3 := by
  have hα : 0 < 1 / k := by positivity
  have hb : 1 / k ≤ b := by rw [div_le_iff₀ hk]; linarith
  have hb0 : 0 < b := hα.trans_le hb
  have hpos : ∀ x ∈ Set.uIcc (1 / k) b, 0 < x := fun x hx => by
    rw [Set.uIcc_of_le hb] at hx; exact hα.trans_le hx.1
  have hu'c : ContinuousOn (fun s : ℝ => -(s ^ 2)⁻¹) (Set.uIcc (1 / k) b) :=
    (ContinuousOn.inv₀ (by fun_prop) fun x hx => pow_ne_zero 2 (hpos x hx).ne').neg
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := fun s => s⁻¹) (u' := fun s => -(s ^ 2)⁻¹)
    (v := fun s => Real.sin (k * s) / k) (v' := fun s => Real.cos (k * s))
    (fun x hx => hasDerivAt_inv (hpos x hx).ne')
    (fun x hx => by
      have := (((hasDerivAt_id x).const_mul k).sin).div_const k
      simp only [id_eq, mul_one] at this
      convert this using 1
      field_simp)
    hu'c.intervalIntegrable
    ((by fun_prop : Continuous fun s => Real.cos (k * s)).intervalIntegrable _ _)
  have e : (∫ s in (1 / k)..b, Real.cos (k * s) / s)
      = ∫ s in (1 / k)..b, s⁻¹ * Real.cos (k * s) := by
    apply intervalIntegral.integral_congr; intro s _; simp only; ring
  rw [e, hparts]
  have t1 : |b⁻¹ * (Real.sin (k * b) / k)| ≤ 1 := by
    rw [abs_mul, abs_div, abs_inv, abs_of_pos hb0, abs_of_pos hk]
    have h1 := Real.abs_sin_le_one (k * b)
    calc b⁻¹ * (|Real.sin (k * b)| / k) ≤ b⁻¹ * (1 / k) := by gcongr
      _ = 1 / (k * b) := by field_simp
      _ ≤ 1 := by rw [div_le_one (by positivity)]; exact hkb
  have t2 : |(1 / k)⁻¹ * (Real.sin (k * (1 / k)) / k)| ≤ 1 := by
    rw [show k * (1 / k) = 1 by field_simp, one_div, inv_inv, mul_div_cancel₀ _ hk.ne']
    exact Real.abs_sin_le_one 1
  have t3 : |∫ s in (1 / k)..b, -(s ^ 2)⁻¹ * (Real.sin (k * s) / k)| ≤ 1 := by
    have hg : IntervalIntegrable (fun s : ℝ => (s ^ 2)⁻¹ * (1 / k)) volume (1 / k) b :=
      ((ContinuousOn.inv₀ (by fun_prop) fun x hx => pow_ne_zero 2 (hpos x hx).ne').mul
        continuousOn_const).intervalIntegrable
    have hle := intervalIntegral.norm_integral_le_of_norm_le hb
      (f := fun s => -(s ^ 2)⁻¹ * (Real.sin (k * s) / k))
      (Eventually.of_forall fun t ht => by
        have ht0 : 0 < t := hα.trans ht.1
        rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_div, abs_of_pos hk,
          abs_of_pos (inv_pos.2 (pow_pos ht0 2))]
        gcongr
        exact Real.abs_sin_le_one _) hg
    rw [Real.norm_eq_abs] at hle
    refine hle.trans ?_
    have hF : ∀ x ∈ Set.uIcc (1 / k) b,
        HasDerivAt (fun s : ℝ => -s⁻¹) ((x ^ 2)⁻¹) x := fun x hx => by
      have := (hasDerivAt_inv (hpos x hx).ne').neg
      rwa [neg_neg] at this
    rw [intervalIntegral.integral_mul_const,
      intervalIntegral.integral_eq_sub_of_hasDerivAt hF
        ((ContinuousOn.inv₀ (by fun_prop) fun x hx =>
          pow_ne_zero 2 (hpos x hx).ne').intervalIntegrable)]
    rw [one_div, inv_inv]
    have : (-b⁻¹ - -k) * k⁻¹ = 1 - 1 / (k * b) := by field_simp; ring
    rw [this]
    have : 0 < 1 / (k * b) := by positivity
    linarith
  calc |b⁻¹ * (Real.sin (k * b) / k) - (1 / k)⁻¹ * (Real.sin (k * (1 / k)) / k)
        - ∫ s in (1 / k)..b, -(s ^ 2)⁻¹ * (Real.sin (k * s) / k)|
      ≤ |b⁻¹ * (Real.sin (k * b) / k) - (1 / k)⁻¹ * (Real.sin (k * (1 / k)) / k)|
        + |∫ s in (1 / k)..b, -(s ^ 2)⁻¹ * (Real.sin (k * s) / k)| := abs_sub _ _
    _ ≤ (|b⁻¹ * (Real.sin (k * b) / k)| + |(1 / k)⁻¹ * (Real.sin (k * (1 / k)) / k)|)
        + |∫ s in (1 / k)..b, -(s ^ 2)⁻¹ * (Real.sin (k * s) / k)| := by
        gcongr; exact abs_sub _ _
    _ ≤ 3 := by linarith

theorem one_sub_cos_nonneg' (x : ℝ) : 0 ≤ 2 - 2 * Real.cos x := by
  linarith [Real.cos_le_one x]

/-- The weight is integrable on `(0, b]`: `0 ≤ (2 − 2cos ks)/s ≤ k²s`. -/
theorem integrableOn_weight (b k : ℝ) :
    IntegrableOn (fun s => (2 - 2 * Real.cos (k * s)) / s) (Ioc 0 b) := by
  have hfin : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) b)) :=
    isFiniteMeasure_restrict.2 measure_Ioc_lt_top.ne
  have hm : AEStronglyMeasurable (fun s => (2 - 2 * Real.cos (k * s)) / s)
      (volume.restrict (Ioc 0 b)) := by
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioc
    exact ContinuousOn.div (by fun_prop) continuousOn_id fun x hx => hx.1.ne'
  refine (integrable_const (k ^ 2 * |b|)).mono' hm ?_
  refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun s hs => ?_)
  have hs0 : 0 < s := hs.1
  have hc := Real.one_sub_sq_div_two_le_cos (x := k * s)
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (one_sub_cos_nonneg' _) hs0.le),
    div_le_iff₀ hs0]
  have hsb : s ≤ |b| := hs.2.trans (le_abs_self b)
  nlinarith [sq_nonneg k, mul_le_mul_of_nonneg_left hsb (sq_nonneg k), sq_nonneg s]

/-- **`J(k) = ∫₀^b (2 − 2cos ks)/s ds ≥ 2 log(kb) − 6`** for `kb ≥ 1`. -/
theorem weight_ge {b k : ℝ} (hk : 0 < k) (hkb : 1 ≤ k * b) :
    2 * Real.log (k * b) - 6 ≤ ∫ s in Ioc 0 b, (2 - 2 * Real.cos (k * s)) / s := by
  have hα : 0 < 1 / k := by positivity
  have hb : 1 / k ≤ b := by rw [div_le_iff₀ hk]; linarith
  have hpos : ∀ x ∈ Set.uIcc (1 / k) b, 0 < x := fun x hx => by
    rw [Set.uIcc_of_le hb] at hx; exact hα.trans_le hx.1
  have hmono : (∫ s in Ioc (1 / k) b, (2 - 2 * Real.cos (k * s)) / s)
      ≤ ∫ s in Ioc 0 b, (2 - 2 * Real.cos (k * s)) / s :=
    setIntegral_mono_set (integrableOn_weight b k)
      ((ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun s hs =>
        div_nonneg (one_sub_cos_nonneg' _) hs.1.le))
      (Ioc_subset_Ioc_left hα.le).eventuallyLE
  refine le_trans ?_ hmono
  rw [← intervalIntegral.integral_of_le hb]
  have hi1 : IntervalIntegrable (fun s : ℝ => 2 * s⁻¹) volume (1 / k) b :=
    (continuousOn_const.mul (ContinuousOn.inv₀ continuousOn_id fun x hx =>
      (hpos x hx).ne')).intervalIntegrable
  have hi2 : IntervalIntegrable (fun s : ℝ => 2 * (Real.cos (k * s) / s)) volume (1 / k) b :=
    (continuousOn_const.mul (ContinuousOn.div (by fun_prop) continuousOn_id fun x hx =>
      (hpos x hx).ne')).intervalIntegrable
  have e : (∫ s in (1 / k)..b, (2 - 2 * Real.cos (k * s)) / s)
      = (∫ s in (1 / k)..b, 2 * s⁻¹) - ∫ s in (1 / k)..b, 2 * (Real.cos (k * s) / s) := by
    rw [← intervalIntegral.integral_sub hi1 hi2]
    apply intervalIntegral.integral_congr; intro s _; simp only; ring
  rw [e, intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_inv_of_pos hα (hα.trans_le hb), show b / (1 / k) = k * b by field_simp]
  have := abs_integral_cos_div_le hk hkb
  have := neg_abs_le (∫ s in (1 / k)..b, Real.cos (k * s) / s)
  have := le_abs_self (∫ s in (1 / k)..b, Real.cos (k * s) / s)
  linarith

/-! ## The energy dominates the weighted coefficients -/

/-- The weight of frequency `n`: `J_n = ∫₀^b (2 − 2cos(2πns/4a))/s ds`. -/
def wJ (a b : ℝ) (n : ℤ) : ℝ := ∫ s in Ioc 0 b, (2 - 2 * Real.cos (2 * π * n * s / (4 * a))) / s

/-- The archimedean energy `E(g) = ∫₀^∞ [f(0) − f(u)] e^{u/2}/sinh u du`. -/
def archE (g : ℝ → ℝ) : ℝ := ∫ u in Ioi (0 : ℝ), archIntegrand g u

theorem archIntegrand_nonneg {g : ℝ → ℝ} (hg : MemLp g 2 volume) {u : ℝ} (hu : 0 < u) :
    0 ≤ archIntegrand g u := by
  refine mul_nonneg ?_ (div_pos (Real.exp_pos _) (Real.sinh_pos_iff.2 hu)).le
  rw [autocorr_zero, sub_nonneg]
  exact (le_abs_self _).trans (abs_autocorr_le hg u)

/-- **`a Σ_{n∈S} |c_n|² J_n ≤ E(g)`** for every finite set of frequencies, `0 < b ≤ 1`, `b < a`. -/
theorem weighted_le_archE {a : ℝ} (ha : 0 < a) {g : ℝ → ℝ} (hp : Probe a g) {b : ℝ}
    (hb1 : b ≤ 1) (hba : b < a) (S : Finset ℤ) :
    a * ∑ n ∈ S, ‖cf a g n‖ ^ 2 * wJ a b n ≤ archE g := by
  set G : ℝ → ℝ := fun s =>
    a * ∑ n ∈ S, ‖cf a g n‖ ^ 2 * ((2 - 2 * Real.cos (2 * π * n * s / (4 * a))) / s) with hG
  have hwint : ∀ n : ℤ, IntegrableOn
      (fun s => (2 - 2 * Real.cos (2 * π * n * s / (4 * a))) / s) (Ioc 0 b) := by
    intro n
    have := integrableOn_weight b (2 * π * n / (4 * a))
    refine this.congr_fun (fun s _ => ?_) measurableSet_Ioc
    simp only; congr 3; ring_nf
  have hGint : IntegrableOn G (Ioc 0 b) :=
    (integrable_finsetSum S fun n _ => (hwint n).const_mul _).const_mul a
  have hLHS : a * ∑ n ∈ S, ‖cf a g n‖ ^ 2 * wJ a b n = ∫ s in Ioc 0 b, G s := by
    rw [hG, integral_const_mul, integral_finsetSum S fun n _ => (hwint n).const_mul _]
    congr 1
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [integral_const_mul]; rfl
  rw [hLHS]
  have harch_nonneg : ∀ u ∈ Ioi (0 : ℝ), 0 ≤ archIntegrand g u :=
    fun u hu => archIntegrand_nonneg hp.memL2 hu
  calc (∫ s in Ioc 0 b, G s) ≤ ∫ s in Ioc 0 b, archIntegrand g s := by
        refine setIntegral_mono_on hGint (hp.arch.mono_set Ioc_subset_Ioi_self)
          measurableSet_Ioc fun s hs => ?_
        have hs0 : 0 < s := hs.1
        have hsa : |s| < a := by rw [abs_of_pos hs0]; linarith [hs.2]
        have hH := hasSum_shift ha hp hsa
        have hsum := sum_le_hasSum S (fun n _ => mul_nonneg (sq_nonneg _)
          (one_sub_cos_nonneg' _)) hH
        have hK := archK_ge hs0 (hs.2.trans hb1)
        have hf : 0 ≤ autocorr g 0 - autocorr g s := by
          rw [autocorr_zero, sub_nonneg]
          exact (le_abs_self _).trans (abs_autocorr_le hp.memL2 s)
        unfold archIntegrand
        have e : G s = (a / s) * ∑ n ∈ S, ‖cf a g n‖ ^ 2
            * (2 - 2 * Real.cos (2 * π * n * s / (4 * a))) := by
          rw [hG]; simp only
          rw [Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun n _ => ?_
          field_simp
        rw [e]
        calc (a / s) * ∑ n ∈ S, ‖cf a g n‖ ^ 2 * (2 - 2 * Real.cos (2 * π * n * s / (4 * a)))
            ≤ (a / s) * ((4 * a)⁻¹ * (2 * (autocorr g 0 - autocorr g s))) :=
              mul_le_mul_of_nonneg_left hsum (by positivity)
          _ = (autocorr g 0 - autocorr g s) * (1 / (2 * s)) := by field_simp; ring
          _ ≤ (autocorr g 0 - autocorr g s) * (Real.exp (s / 2) / Real.sinh s) :=
              mul_le_mul_of_nonneg_left hK hf
    _ ≤ archE g :=
        setIntegral_mono_set hp.arch
          ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall harch_nonneg))
          Ioc_subset_Ioi_self.eventuallyLE

/-- The weight is even in `n` and `≥ 2 log(2π|n|b/4a) − 6` once `2π|n|b/4a ≥ 1`. -/
theorem wJ_ge {a b : ℝ} (ha : 0 < a) {n : ℤ} (hn : 1 ≤ 2 * π * |(n : ℝ)| / (4 * a) * b) :
    2 * Real.log (2 * π * |(n : ℝ)| / (4 * a) * b) - 6 ≤ wJ a b n := by
  have hk : 0 < 2 * π * |(n : ℝ)| / (4 * a) := by
    have hn0 : (n : ℝ) ≠ 0 := by
      rintro h; rw [h, abs_zero] at hn; simp at hn; linarith
    have := abs_pos.2 hn0
    positivity
  refine (weight_ge hk hn).trans (le_of_eq ?_)
  unfold wJ
  refine setIntegral_congr_fun measurableSet_Ioc fun s hs => ?_
  congr 2
  rw [← Real.cos_abs (2 * π * n * s / (4 * a))]
  congr 1
  rw [abs_div, abs_mul, abs_mul, abs_mul, abs_of_pos hs.1, abs_of_pos (by positivity : (0:ℝ) < 4 * a),
    abs_of_pos Real.pi_pos, abs_two]
  ring_nf

/-- **The tail bound**: if `κ = 2πNb/4a ≥ 1` and `L = 2 log κ − 6 > 0`, then
`Σ_{|n| ≥ N} |c_n|² ≤ E(g)/(aL)`, uniformly in the probe. -/
theorem tail_le {a : ℝ} (ha : 0 < a) {g : ℝ → ℝ} (hp : Probe a g) {b : ℝ}
    (hb0 : 0 < b) (hb1 : b ≤ 1) (hba : b < a) {N : ℕ}
    (hN : 1 ≤ 2 * π * N / (4 * a) * b) (hL : 0 < 2 * Real.log (2 * π * N / (4 * a) * b) - 6) :
    (∑' n : ℤ, if (N : ℝ) ≤ |(n : ℝ)| then ‖cf a g n‖ ^ 2 else 0)
      ≤ archE g / (a * (2 * Real.log (2 * π * N / (4 * a) * b) - 6)) := by
  set L := 2 * Real.log (2 * π * N / (4 * a) * b) - 6 with hLdef
  have hE0 : 0 ≤ archE g :=
    setIntegral_nonneg measurableSet_Ioi fun u hu => archIntegrand_nonneg hp.memL2 hu
  refine tsum_le_of_sum_le' (by positivity) fun S => ?_
  rw [le_div_iff₀ (by positivity)]
  set T := S.filter fun n : ℤ => (N : ℝ) ≤ |(n : ℝ)|
  have h1 : (∑ n ∈ S, if (N : ℝ) ≤ |(n : ℝ)| then ‖cf a g n‖ ^ 2 else 0)
      = ∑ n ∈ T, ‖cf a g n‖ ^ 2 := by rw [Finset.sum_filter]
  have h2 : ∀ n ∈ T, L ≤ wJ a b n := by
    intro n hn
    have hnN : (N : ℝ) ≤ |(n : ℝ)| := (Finset.mem_filter.1 hn).2
    have hmono : 2 * π * N / (4 * a) * b ≤ 2 * π * |(n : ℝ)| / (4 * a) * b := by
      gcongr
    refine le_trans ?_ (wJ_ge ha (hN.trans hmono))
    have : Real.log (2 * π * N / (4 * a) * b) ≤ Real.log (2 * π * |(n : ℝ)| / (4 * a) * b) :=
      Real.log_le_log (by linarith) hmono
    rw [hLdef]; linarith
  rw [h1]
  calc (∑ n ∈ T, ‖cf a g n‖ ^ 2) * (a * L) = a * ∑ n ∈ T, ‖cf a g n‖ ^ 2 * L := by
        rw [Finset.sum_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun n _ => by ring
    _ ≤ a * ∑ n ∈ T, ‖cf a g n‖ ^ 2 * wJ a b n := by
        gcongr with n hn
        exact h2 n hn
    _ ≤ archE g := weighted_le_archE ha hp hb1 hba T

end Pilot1ca

#print axioms Pilot1ca.normSq_sub_shift
#print axioms Pilot1ca.hasSum_cf_sq
#print axioms Pilot1ca.cf_shift
#print axioms Pilot1ca.hasSum_shift
#print axioms Pilot1ca.archK_ge
#print axioms Pilot1ca.weight_ge
#print axioms Pilot1ca.weighted_le_archE
#print axioms Pilot1ca.tail_le
