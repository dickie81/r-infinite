import Mathlib
import Mollify

/-! # The explicit-formula bridge: `weilQ` is the zero side of Weil's explicit formula (round 126)

Four places in the pilot assume "Weil's explicit formula" in four shapes: `T1bt`'s `h_explicit`,
Exterior.lean's `WeilExplicit`, and the `hQ` hypotheses of Saturation.lean and Unconditional.lean.
Nothing connected `WeilExplicit` (the classical Guinand–Weil statement, for a test function `h`) to
the pilot's own `weilQ` (the prime-side form of Theorem 1bn(i)). This file proves the connection:

  `WeilExplicit ρ ĝ² ĝ²|ℝ` and `DigammaDiff`  ⟹  `Σ_ρ ĝ(t_ρ)² = weilQ a g`   (`weilQ_eq_zero_sum`)

for every even probe `g`. So `WeilExplicit` is the one named input, and the other three shapes follow.

**Proved here (no new input).**
* **The pole terms.** `h(±i/2) = ĝ(i/2)² = poleR²` (`ghatC_I_div_two`, evenness).
* **The convolution identity** (`fourier_autocorr`): `∫ f(x)e^{irx} dx = ĝ(r)²` with `f = autocorr g`.
* **`∫ĝ² < ∞`** (`integrable_hsq`): `ĝ² ≥ 0` is the Fourier transform of `f`. Regularising with
  Gaussians and using Mathlib's Gaussian Fourier transform gives `∫ e^{−x²/c}ĝ² → 2πf(0)`, and monotone
  convergence does the rest (a Bochner-type argument; no Plancherel needed).
* **Fourier inversion** (`gh_hsq`): `g_h = f`, i.e. `(1/2π)∫ĝ(r)² cos(ru) dr = f(u)`, from Mathlib's
  `Continuous.fourierInv_fourier_eq`. So the constant and prime terms of `WeilExplicit` are `weilQ`'s.
* **The archimedean term**, given `DigammaDiff` (next item), by Tonelli and `t = 2u`:
  `(1/2π)∫ĝ² Re ψ(¼ + ir/2) = Re ψ(¼)‖g‖² + archE g`.

**The new named input `DigammaDiff`**: `ψ(z) − ψ(w) = ∫_0^∞ (e^{−wt} − e^{−zt})/(1 − e^{−t}) dt` for
`Re z, Re w > 0`. This is Gauss's integral representation of the digamma function, in difference form.
Mathlib's `Digamma.lean` lists it as a TODO, so it enters as a hypothesis, like `BinetFormula`
(Exterior.lean) does.
-/

open Real Filter Topology Complex MeasureTheory Set
open scoped FourierTransform

noncomputable section

namespace Pilot1ca

/-! ## A1. The transform on the real line, and the convolution identity -/

variable {a : ℝ} {g : ℝ → ℝ}

/-- `ĝ(r)` for real `r`, as a real number (it is real for even `g`). -/
def gH (g : ℝ → ℝ) (a r : ℝ) : ℝ := (ghatC g a r).re

theorem ghatC_real (hp : Probe a g) (ha : 0 ≤ a) (r : ℝ) : ghatC g a r = (gH g a r : ℂ) := by
  apply Complex.ext
  · simp [gH]
  · simp [ghatC_im_zero hp.memL2 hp.even ha r]

theorem gH_neg (hp : Probe a g) (r : ℝ) : gH g a (-r) = gH g a r := by
  unfold gH; rw [Complex.ofReal_neg, ghatC_neg_of_even hp.memL2 hp.even]

theorem continuous_gH (hp : Probe a g) : Continuous (gH g a) :=
  Complex.continuous_re.comp
    ((ghatC_differentiable (probe_integrable hp).intervalIntegrable).continuous.comp
      Complex.continuous_ofReal)

/-- `|ĝ(r)| ≤ ‖g‖₁` on the real line. -/
theorem abs_gH_le (hp : Probe a g) (ha : 0 < a) (r : ℝ) : |gH g a r| ≤ ∫ u, |g u| := by
  have h1 : |gH g a r| ≤ ‖ghatC g a r‖ := Complex.abs_re_le_norm _
  refine h1.trans ?_
  rw [ghatC_eq_integral ha hp.supp]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  congr 1; funext u
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]
  have : (Complex.I * (r : ℂ) * (u : ℂ)).re = 0 := by simp
  rw [this, Real.exp_zero, mul_one]

/-- For even `g`, `f(x) = ∫ g(t)g(x − t) dt`: the autocorrelation is a convolution. -/
theorem autocorr_eq_conv (heven : ∀ u, g (-u) = g u) (x : ℝ) :
    autocorr g x = ∫ t, g t * g (x - t) := by
  unfold autocorr
  rw [← integral_neg_eq_self (fun t => g t * g (t + x))]
  congr 1; funext t
  rw [heven, show -t + x = x - t by ring]

/-- **The convolution identity**: `∫ f(x) e^{irx} dx = ĝ(r)²`. -/
theorem fourier_autocorr (hp : Probe a g) (ha : 0 < a) (r : ℝ) :
    ∫ x, (autocorr g x : ℂ) * Complex.exp (Complex.I * r * x) = ghatC g a r ^ 2 := by
  have hg := probe_integrable hp
  set e : ℝ → ℂ := fun x => Complex.exp (Complex.I * r * x) with he
  have he1 : ∀ x, ‖e x‖ = 1 := fun x => by
    simp only [he, Complex.norm_exp]
    have : (Complex.I * (r : ℂ) * (x : ℂ)).re = 0 := by simp
    rw [this, Real.exp_zero]
  have h0 := hg.convolution_integrand (L := ContinuousLinearMap.mul ℝ ℝ) hg (μ := volume) (ν := volume)
  simp only [ContinuousLinearMap.mul_apply'] at h0
  have hF : Integrable (Function.uncurry fun x t : ℝ => ((g t * g (x - t) : ℝ) : ℂ) * e x)
      (volume.prod volume) := by
    refine Integrable.mono' h0.norm
      ((Complex.continuous_ofReal.comp_aestronglyMeasurable h0.aestronglyMeasurable).mul
        ((by fun_prop : Continuous fun p : ℝ × ℝ => e p.1).aestronglyMeasurable)) ?_
    refine Eventually.of_forall fun p => ?_
    show ‖((g p.2 * g (p.1 - p.2) : ℝ) : ℂ) * e p.1‖ ≤ _
    rw [norm_mul, he1, mul_one, Complex.norm_real]
  have hinner : ∀ t, ∫ x, ((g t * g (x - t) : ℝ) : ℂ) * e x = ((g t : ℂ) * e t) * ghatC g a r := by
    intro t
    have e1 : (fun x => ((g t * g (x - t) : ℝ) : ℂ) * e x)
        = fun x => ((g t : ℂ) * e t) * (fun y => ((g y : ℝ) : ℂ) * e y) (x - t) := by
      funext x
      simp only [he]
      rw [show Complex.I * (r : ℂ) * (x : ℂ) = Complex.I * r * t + Complex.I * r * ((x - t : ℝ) : ℂ) by
        push_cast; ring, Complex.exp_add]
      push_cast; ring
    rw [e1, integral_const_mul, integral_sub_right_eq_self (fun y => ((g y : ℝ) : ℂ) * e y) t,
      ghatC_eq_integral ha hp.supp]
  calc ∫ x, (autocorr g x : ℂ) * e x
      = ∫ x, ∫ t, ((g t * g (x - t) : ℝ) : ℂ) * e x := by
        congr 1; funext x
        rw [autocorr_eq_conv hp.even, ← integral_complex_ofReal, ← integral_mul_const]
    _ = ∫ t, ∫ x, ((g t * g (x - t) : ℝ) : ℂ) * e x := integral_integral_swap hF
    _ = ∫ t, ((g t : ℂ) * e t) * ghatC g a r := by congr 1; funext t; exact hinner t
    _ = ghatC g a r ^ 2 := by
        rw [integral_mul_const, ← ghatC_eq_integral ha hp.supp, sq]

/-! ## A2. The autocorrelation in Mathlib's Fourier normalisation -/

theorem continuous_autocorr (hg : MemLp g 2 volume) : Continuous (autocorr g) := by
  have e : autocorr g = fun v => autocorr g 0 - Fsh g v / 2 := by
    funext v; unfold Fsh; rw [normSq_sub_shift hg v]; ring
  rw [e]; exact continuous_const.sub ((Fsh_continuous hg).div_const 2)

theorem integrable_autocorr (hp : Probe a g) (ha : 0 < a) : Integrable (autocorr g) := by
  refine (continuous_autocorr hp.memL2).integrable_of_hasCompactSupport ?_
  refine HasCompactSupport.intro (isCompact_Icc (a := -(2 * a)) (b := 2 * a)) fun u hu => ?_
  apply autocorr_eq_zero hp.supp
  simp only [mem_Icc, not_and_or, not_le] at hu
  rcases hu with h | h
  · rw [abs_of_neg (by linarith)]; linarith
  · rw [abs_of_pos (by linarith)]; exact h

/-- `ĝ(2πξ)²`: Mathlib's Fourier transform of `f`. -/
def PhiH (g : ℝ → ℝ) (a ξ : ℝ) : ℝ := gH g a (2 * π * ξ) ^ 2

theorem fourier_autocorr_eq (hp : Probe a g) (ha : 0 < a) (ξ : ℝ) :
    𝓕 (fun x : ℝ => (autocorr g x : ℂ)) ξ = (PhiH g a ξ : ℂ) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  have e : (fun v : ℝ => Complex.exp (↑(-2 * π * v * ξ) * Complex.I) • (autocorr g v : ℂ))
      = fun v => (autocorr g v : ℂ) * Complex.exp (Complex.I * ((-(2 * π * ξ) : ℝ) : ℂ) * v) := by
    funext v; rw [smul_eq_mul, mul_comm]; congr 2; push_cast; ring
  rw [e, fourier_autocorr hp ha, ghatC_real hp ha.le, gH_neg hp, PhiH]; push_cast; rfl

/-! ## A3. `∫ĝ² < ∞`, by Gaussian regularisation -/

/-- `∫ e^{−x²/c} ĝ(2πx)² dx → f(0)` as `c → ∞`. -/
theorem tendsto_gauss_PhiH (hp : Probe a g) (ha : 0 < a) :
    Tendsto (fun c : ℝ => ∫ x, Real.exp (-c⁻¹ * x ^ 2) * PhiH g a x) atTop (𝓝 (autocorr g 0)) := by
  set F : ℝ → ℂ := fun x => (autocorr g x : ℂ) with hF
  have hFi : Integrable F := (integrable_autocorr hp ha).ofReal
  have hFc : Continuous F := Complex.continuous_ofReal.comp (continuous_autocorr hp.memL2)
  have hT := Real.tendsto_integral_gaussian_smul' hFi (v := (0 : ℝ)) hFc.continuousAt
  have key : ∀ c : ℝ, 0 < c →
      (∫ w : ℝ, ((π * c : ℂ) ^ (Module.finrank ℝ ℝ / 2 : ℂ)
          * cexp (-π ^ 2 * c * ‖(0 : ℝ) - w‖ ^ 2)) • F w)
        = ((∫ x, Real.exp (-c⁻¹ * x ^ 2) * PhiH g a x : ℝ) : ℂ) := by
    intro c hc
    have hb : 0 < ((c : ℂ)⁻¹).re := by simp; positivity
    have hJ : Integrable (fun w : ℝ => cexp (-((c : ℂ))⁻¹ * ‖w‖ ^ 2)) := by
      simpa using GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := ℝ) hb 0 0
    have hflip := VectorFourier.integral_fourierIntegral_smul_eq_flip (L := innerₗ ℝ)
      Real.continuous_fourierChar continuous_inner hJ hFi
    simp only [flip_innerₗ] at hflip
    change ∫ ξ, 𝓕 (fun w : ℝ => cexp (-((c : ℂ))⁻¹ * ‖w‖ ^ 2)) ξ • F ξ
      = ∫ x, cexp (-((c : ℂ))⁻¹ * ‖x‖ ^ 2) • 𝓕 F x at hflip
    simp_rw [fourier_gaussian_innerProductSpace (V := ℝ) hb] at hflip
    have e1 : (fun w : ℝ => ((π * c : ℂ) ^ (Module.finrank ℝ ℝ / 2 : ℂ)
          * cexp (-π ^ 2 * c * ‖(0 : ℝ) - w‖ ^ 2)) • F w)
        = fun ξ : ℝ => (((π : ℂ) / ((c : ℂ))⁻¹) ^ ((Module.finrank ℝ ℝ : ℂ) / 2)
          * cexp (-(π : ℂ) ^ 2 * ‖ξ‖ ^ 2 / ((c : ℂ))⁻¹)) • F ξ := by
      funext w
      rw [div_inv_eq_mul, zero_sub, norm_neg, div_inv_eq_mul]
      congr 3; ring
    rw [e1, hflip, ← integral_complex_ofReal]
    congr 1; funext x
    have hx : 𝓕 F x = (PhiH g a x : ℂ) := fourier_autocorr_eq hp ha x
    have hx2 : ((‖x‖ : ℝ) : ℂ) ^ 2 = (x : ℂ) ^ 2 := by
      rw [← Complex.ofReal_pow, Real.norm_eq_abs, sq_abs, Complex.ofReal_pow]
    rw [hx, smul_eq_mul, Complex.ofReal_mul, Complex.ofReal_exp, hx2]
    push_cast; ring_nf
  have hT' : Tendsto (fun c : ℝ => ((∫ x, Real.exp (-c⁻¹ * x ^ 2) * PhiH g a x : ℝ) : ℂ)) atTop
      (𝓝 (F 0)) :=
    hT.congr' ((eventually_gt_atTop 0).mono fun c hc => key c hc)
  have := (Complex.continuous_re.tendsto _).comp hT'
  simpa [hF, Function.comp_def] using this

theorem PhiH_nonneg (x : ℝ) : 0 ≤ PhiH g a x := sq_nonneg _

theorem continuous_PhiH (hp : Probe a g) : Continuous (PhiH g a) :=
  ((continuous_gH hp).comp (continuous_const.mul continuous_id)).pow 2

theorem PhiH_le (hp : Probe a g) (ha : 0 < a) (x : ℝ) : PhiH g a x ≤ (∫ u, |g u|) ^ 2 := by
  unfold PhiH
  rw [← sq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) (abs_gH_le hp ha _) 2

/-- **`ĝ(2π·)²` is integrable**: monotone convergence along the Gaussian regularisation. -/
theorem integrable_PhiH (hp : Probe a g) (ha : 0 < a) : Integrable (PhiH g a) := by
  set C := (∫ u, |g u|) ^ 2
  have hk : ∀ n : ℕ, Integrable (fun x => Real.exp (-((n : ℝ) + 1)⁻¹ * x ^ 2) * PhiH g a x) := by
    intro n
    refine (integrable_exp_neg_mul_sq (by positivity : (0 : ℝ) < ((n : ℝ) + 1)⁻¹)).mul_bdd
      (continuous_PhiH hp).aestronglyMeasurable (c := C) (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (PhiH_nonneg x)]; exact PhiH_le hp ha x
  have hkn : ∀ n : ℕ, ∀ x, 0 ≤ Real.exp (-((n : ℝ) + 1)⁻¹ * x ^ 2) * PhiH g a x :=
    fun n x => mul_nonneg (Real.exp_pos _).le (PhiH_nonneg x)
  have hlim : Tendsto (fun n : ℕ => ∫⁻ x, ENNReal.ofReal (Real.exp (-((n : ℝ) + 1)⁻¹ * x ^ 2)
      * PhiH g a x)) atTop (𝓝 (∫⁻ x, ENNReal.ofReal (PhiH g a x))) := by
    refine lintegral_tendsto_of_tendsto_of_monotone (fun n => ?_) ?_ ?_
    · exact ((Real.continuous_exp.comp (continuous_const.mul (continuous_pow 2))).mul
        (continuous_PhiH hp)).measurable.ennreal_ofReal.aemeasurable
    · refine Eventually.of_forall fun x => fun m n hmn => ENNReal.ofReal_le_ofReal ?_
      refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_) (PhiH_nonneg x)
      have h1 : ((n : ℝ) + 1)⁻¹ ≤ ((m : ℝ) + 1)⁻¹ :=
        inv_anti₀ (by positivity) (by exact_mod_cast Nat.add_le_add_right hmn 1)
      nlinarith [sq_nonneg x]
    · refine Eventually.of_forall fun x => ENNReal.tendsto_ofReal ?_
      have h0 : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat.congr fun n => by rw [one_div]
      have h1 : Tendsto (fun n : ℕ => -((n : ℝ) + 1)⁻¹ * x ^ 2) atTop (𝓝 0) := by
        simpa using h0.neg.mul_const (x ^ 2)
      have := ((Real.continuous_exp.tendsto 0).comp h1).mul_const (PhiH g a x)
      simpa using this
  have hval : Tendsto (fun n : ℕ => ∫⁻ x, ENNReal.ofReal (Real.exp (-((n : ℝ) + 1)⁻¹ * x ^ 2)
      * PhiH g a x)) atTop (𝓝 (ENNReal.ofReal (autocorr g 0))) := by
    have hc : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
    have := ENNReal.tendsto_ofReal ((tendsto_gauss_PhiH hp ha).comp hc)
    refine this.congr fun n => ?_
    simp only [Function.comp]
    exact ofReal_integral_eq_lintegral_ofReal (hk n) (Eventually.of_forall (hkn n))
  have heq := tendsto_nhds_unique hlim hval
  refine ⟨(continuous_PhiH hp).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall PhiH_nonneg), heq]
  exact ENNReal.ofReal_lt_top

/-! ## A4. Fourier inversion: `g_h = f` for `h = ĝ²` -/

/-- `h(r) = ĝ(r)²` on the real line. -/
def hsq (g : ℝ → ℝ) (a r : ℝ) : ℝ := gH g a r ^ 2

theorem hsq_nonneg (r : ℝ) : 0 ≤ hsq g a r := sq_nonneg _

theorem integrable_hsq (hp : Probe a g) (ha : 0 < a) : Integrable (hsq g a) :=
  (integrable_comp_mul_left_iff (hsq g a) (by positivity : (2 * π : ℝ) ≠ 0)).1 (integrable_PhiH hp ha)

/-- **Fourier inversion for `f`**: `f(u) = ∫ ĝ(2πv)² cos(2πvu) dv`. -/
theorem autocorr_eq_inv (hp : Probe a g) (ha : 0 < a) (u : ℝ) :
    autocorr g u = ∫ v, PhiH g a v * Real.cos (2 * π * v * u) := by
  set F : ℝ → ℂ := fun x => (autocorr g x : ℂ) with hF
  have hFi : Integrable F := (integrable_autocorr hp ha).ofReal
  have hFc : Continuous F := Complex.continuous_ofReal.comp (continuous_autocorr hp.memL2)
  have hFF : 𝓕 F = fun ξ => (PhiH g a ξ : ℂ) := funext (fourier_autocorr_eq hp ha)
  have hFFi : Integrable (𝓕 F) := by rw [hFF]; exact (integrable_PhiH hp ha).ofReal
  have h := congrFun (Continuous.fourierInv_fourier_eq hFc hFi hFFi) u
  rw [Real.fourierInv_eq', hFF] at h
  simp only [RCLike.inner_apply, conj_trivial] at h
  have hI : Integrable (fun v : ℝ => cexp (↑(2 * π * (u * v)) * I) • (PhiH g a v : ℂ)) := by
    refine (integrable_PhiH hp ha).ofReal.bdd_mul (c := 1)
      (by fun_prop : Continuous fun v : ℝ => cexp (↑(2 * π * (u * v)) * I)).aestronglyMeasurable
      (Eventually.of_forall fun v => ?_)
    rw [Complex.norm_exp_ofReal_mul_I]
  have hre := congrArg Complex.re h
  have hre2 : (∫ v : ℝ, cexp (↑(2 * π * (u * v)) * I) • (PhiH g a v : ℂ)).re
      = ∫ v : ℝ, (cexp (↑(2 * π * (u * v)) * I) • (PhiH g a v : ℂ)).re := (integral_re hI).symm
  rw [hre2] at hre
  simp only [hF, Complex.ofReal_re] at hre
  rw [← hre]
  congr 1; funext v
  rw [smul_eq_mul, mul_comm, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re,
    show 2 * π * (u * v) = 2 * π * v * u by ring]

/-- **`g_h = f`**: `(1/2π)∫ĝ(r)² cos(ru) dr = f(u)`. -/
theorem gh_hsq (hp : Probe a g) (ha : 0 < a) (u : ℝ) : gh (hsq g a) u = autocorr g u := by
  rw [autocorr_eq_inv hp ha u, gh]
  have e := Measure.integral_comp_mul_left (fun r => hsq g a r * Real.cos (r * u)) (2 * π)
  have e2 : (fun v => PhiH g a v * Real.cos (2 * π * v * u))
      = fun v => hsq g a (2 * π * v) * Real.cos (2 * π * v * u) := rfl
  rw [e2, e, abs_of_pos (by positivity : (0 : ℝ) < (2 * π)⁻¹), smul_eq_mul, one_div]

/-- `∫ĝ² = 2πf(0) = 2π‖g‖²`. -/
theorem integral_hsq (hp : Probe a g) (ha : 0 < a) : ∫ r, hsq g a r = 2 * π * normSq g := by
  have h := gh_hsq hp ha 0
  rw [gh, autocorr_zero] at h
  simp only [mul_zero, Real.cos_zero, mul_one] at h
  field_simp at h ⊢
  linarith

/-! ## B1. The digamma difference as a positive-kernel integral -/

/-- **Named input: Gauss's digamma integral, in difference form.** For `Re z, Re w > 0`,
`ψ(z) − ψ(w) = ∫_0^∞ (e^{−wt} − e^{−zt})/(1 − e^{−t}) dt`, with the integrand integrable.
(Mathlib's `Digamma.lean` lists the integral representation as a TODO.) -/
def DigammaDiff : Prop :=
  ∀ z w : ℂ, 0 < z.re → 0 < w.re →
    IntegrableOn (fun t : ℝ => (cexp (-(w * t)) - cexp (-(z * t))) / ((1 - Real.exp (-t) : ℝ) : ℂ))
        (Ioi 0) ∧
      Complex.digamma z - Complex.digamma w
        = ∫ t in Ioi (0 : ℝ), (cexp (-(w * t)) - cexp (-(z * t))) / ((1 - Real.exp (-t) : ℝ) : ℂ)

/-- The kernel `e^{−t/4}/(1 − e^{−t})`. -/
def kk (t : ℝ) : ℝ := Real.exp (-(t / 4)) / (1 - Real.exp (-t))

theorem kk_nonneg {t : ℝ} (ht : 0 < t) : 0 ≤ kk t := by
  unfold kk
  have : Real.exp (-t) < 1 := by rw [← Real.exp_zero]; exact Real.exp_lt_exp.2 (by linarith)
  exact div_nonneg (Real.exp_pos _).le (by linarith)

theorem measurable_kk : Measurable kk := by unfold kk; fun_prop

theorem kk_re (r t : ℝ) :
    ((cexp (-(zB 0 * t)) - cexp (-(zB r * t))) / ((1 - Real.exp (-t) : ℝ) : ℂ)).re
      = kk t * (1 - Real.cos (r * (t / 2))) := by
  rw [Complex.div_ofReal_re, Complex.sub_re, Complex.exp_re, Complex.exp_re]
  unfold kk zB
  simp only [Complex.neg_re, Complex.neg_im, Complex.mul_re, Complex.mul_im, Complex.add_re,
    Complex.add_im, Complex.div_re, Complex.div_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, Complex.one_re, Complex.one_im]
  norm_num
  rw [show r * 2 / 4 * t = r * (t / 2) by ring, show (1 : ℝ) / 4 * t = t / 4 by ring]
  ring

/-- **B1**: `Re ψ(¼ + ir/2) − Re ψ(¼) = ∫_0^∞ k(t)(1 − cos(rt/2)) dt`, integrably. -/
theorem psiRe_sub (hD : DigammaDiff) (r : ℝ) :
    IntegrableOn (fun t => kk t * (1 - Real.cos (r * (t / 2)))) (Ioi 0) ∧
      psiRe r - psiRe 0 = ∫ t in Ioi (0 : ℝ), kk t * (1 - Real.cos (r * (t / 2))) := by
  have hz : ∀ s : ℝ, 0 < (zB s).re := fun s => by unfold zB; simp
  obtain ⟨hI, hE⟩ := hD (zB r) (zB 0) (hz r) (hz 0)
  have hI' := hI.re
  simp only [RCLike.re_to_complex, kk_re] at hI'
  refine ⟨hI', ?_⟩
  unfold psiRe
  have h2 := integral_re hI
  simp only [RCLike.re_to_complex, kk_re] at h2
  rw [← Complex.sub_re, hE, ← h2]

/-! ## B2. The archimedean term, by Tonelli and `t = 2u` -/

theorem continuous_hsq (hp : Probe a g) : Continuous (hsq g a) := (continuous_gH hp).pow 2

theorem integral_hsq_cos (hp : Probe a g) (ha : 0 < a) (u : ℝ) :
    ∫ r, hsq g a r * Real.cos (r * u) = 2 * π * autocorr g u := by
  have h := gh_hsq hp ha u
  rw [gh, one_div, inv_mul_eq_iff_eq_mul₀ (by positivity)] at h
  exact h

theorem integrable_hsq_cos (hp : Probe a g) (ha : 0 < a) (u : ℝ) :
    Integrable (fun r => hsq g a r * Real.cos (r * u)) :=
  (integrable_hsq hp ha).mul_bdd (c := 1) (by fun_prop : Continuous fun r : ℝ =>
    Real.cos (r * u)).aestronglyMeasurable
    (Eventually.of_forall fun r => by rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _)

/-- The `t`-integrand after the `r`-integral: `k(t)(f(0) − f(t/2))`. -/
def phiA (g : ℝ → ℝ) (t : ℝ) : ℝ := kk t * (autocorr g 0 - autocorr g (t / 2))

theorem phiA_two_mul (g : ℝ → ℝ) {u : ℝ} (hu : 0 < u) : 2 * phiA g (2 * u) = archIntegrand g u := by
  unfold phiA kk archIntegrand
  rw [show 2 * u / 2 = u by ring, Real.sinh_eq]
  have e1 : Real.exp (-(2 * u / 4)) = Real.exp (-(u / 2)) := by congr 1; ring
  have e2 : Real.exp (-(2 * u)) = Real.exp (-u) * Real.exp (-u) := by
    rw [← Real.exp_add]; congr 1; ring
  have e3 : Real.exp (u / 2) = Real.exp u * Real.exp (-(u / 2)) := by
    rw [← Real.exp_add]; congr 1; ring
  have h1 : Real.exp (-u) < 1 := by rw [← Real.exp_zero]; exact Real.exp_lt_exp.2 (by linarith)
  have h2 : Real.exp u * Real.exp (-u) = 1 := by rw [← Real.exp_add]; simp
  have h3 : 0 < Real.exp (-u) := Real.exp_pos _
  have h4 : 1 - Real.exp (-u) * Real.exp (-u) ≠ 0 := by nlinarith
  have h5 : Real.exp u - Real.exp (-u) ≠ 0 := by
    have : Real.exp (-u) < Real.exp u := Real.exp_lt_exp.2 (by linarith)
    linarith
  rw [e1, e2, e3]
  field_simp
  have : Real.exp u = (Real.exp (-u))⁻¹ := by rw [← Real.exp_neg, neg_neg]
  rw [this]
  have hx4 : 1 - Real.exp (-u) ^ 2 ≠ 0 := by nlinarith
  have hx5 : (Real.exp (-u))⁻¹ - Real.exp (-u) ≠ 0 := by rw [← this]; exact h5
  field_simp

theorem phiA_integrable (hp : Probe a g) : IntegrableOn (phiA g) (Ioi 0) := by
  have h : IntegrableOn (fun u => phiA g (2 * u)) (Ioi 0) := by
    refine IntegrableOn.congr_fun (hp.arch.div_const 2) (fun u hu => ?_) measurableSet_Ioi
    rw [← phiA_two_mul g hu]; ring
  simpa using (integrableOn_Ioi_comp_mul_left_iff (phiA g) 0 (by norm_num : (0 : ℝ) < 2)).1 h

theorem phiA_integral (g : ℝ → ℝ) : ∫ t in Ioi (0 : ℝ), phiA g t = archE g := by
  have e := integral_comp_mul_left_Ioi (phiA g) 0 (by norm_num : (0 : ℝ) < 2)
  simp only [mul_zero, smul_eq_mul] at e
  have e2 : ∫ x in Ioi (0 : ℝ), phiA g (2 * x) = (∫ u in Ioi (0 : ℝ), archIntegrand g u) / 2 := by
    rw [← integral_div]
    refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
    rw [← phiA_two_mul g hu]; ring
  rw [archE]
  linarith

/-- **B2**: `∫ ĝ(r)² (Re ψ(¼ + ir/2) − Re ψ(¼)) dr = 2π·E(g)`, integrably. -/
theorem hsq_psi_sub (hp : Probe a g) (ha : 0 < a) (hD : DigammaDiff) :
    Integrable (fun r => hsq g a r * (psiRe r - psiRe 0)) ∧
      ∫ r, hsq g a r * (psiRe r - psiRe 0) = 2 * π * archE g := by
  set ν := volume.restrict (Ioi (0 : ℝ))
  set F : ℝ × ℝ → ℝ := fun p => hsq g a p.1 * (kk p.2 * (1 - Real.cos (p.1 * (p.2 / 2)))) with hFd
  have hFm : AEStronglyMeasurable F (volume.prod ν) := by
    refine Measurable.aestronglyMeasurable ?_
    refine ((continuous_hsq hp).measurable.comp measurable_fst).mul
      ((measurable_kk.comp measurable_snd).mul ?_)
    exact (Continuous.measurable (by fun_prop))
  have hinner : ∀ t, ∫ r, F (r, t) = 2 * π * phiA g t := by
    intro t
    have e : (fun r => F (r, t))
        = fun r => kk t * (hsq g a r - hsq g a r * Real.cos (r * (t / 2))) := by
      funext r; simp only [hFd]; ring
    rw [e, integral_const_mul, integral_sub (integrable_hsq hp ha) (integrable_hsq_cos hp ha _),
      integral_hsq hp ha, integral_hsq_cos hp ha, ← autocorr_zero, phiA]
    ring
  have hFint : ∀ t, Integrable (fun r => F (r, t)) := by
    intro t
    have e : (fun r => F (r, t))
        = fun r => kk t * (hsq g a r - hsq g a r * Real.cos (r * (t / 2))) := by
      funext r; simp only [hFd]; ring
    rw [e]; exact ((integrable_hsq hp ha).sub (integrable_hsq_cos hp ha _)).const_mul _
  have hFnn : ∀ r, ∀ t, 0 < t → 0 ≤ F (r, t) := fun r t ht =>
    mul_nonneg (hsq_nonneg r) (mul_nonneg (kk_nonneg ht) (by linarith [Real.cos_le_one (r * (t / 2))]))
  have hF : Integrable F (volume.prod ν) := by
    rw [integrable_prod_iff' hFm]
    refine ⟨Eventually.of_forall hFint, ?_⟩
    refine ((phiA_integrable hp).const_mul (2 * π)).congr ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_)
    show 2 * π * phiA g t = ∫ r, ‖F (r, t)‖
    rw [← hinner t]
    congr 1; funext r
    rw [Real.norm_eq_abs, abs_of_nonneg (hFnn r t ht)]
  have hG : ∀ r, ∫ t, F (r, t) ∂ν = hsq g a r * (psiRe r - psiRe 0) := by
    intro r
    simp only [hFd, ν]
    rw [integral_const_mul, (psiRe_sub hD r).2]
  have hGi := hF.integral_prod_left
  simp only [hG] at hGi
  refine ⟨hGi, ?_⟩
  calc ∫ r, hsq g a r * (psiRe r - psiRe 0) = ∫ r, ∫ t, F (r, t) ∂ν := by simp only [hG]
    _ = ∫ t, (∫ r, F (r, t)) ∂ν := integral_integral_swap (f := fun r t => F (r, t)) hF
    _ = ∫ t in Ioi (0 : ℝ), 2 * π * phiA g t := by simp only [hinner, ν]
    _ = 2 * π * archE g := by rw [integral_const_mul, phiA_integral g]

/-- `(1/2π)∫ ĝ² Re ψ(¼ + ir/2) = Re ψ(¼)‖g‖² + E(g)`. -/
theorem arch_term (hp : Probe a g) (ha : 0 < a) (hD : DigammaDiff) :
    1 / (2 * π) * ∫ r, hsq g a r * psiRe r = psiRe 0 * normSq g + archE g := by
  obtain ⟨hi, he⟩ := hsq_psi_sub hp ha hD
  have e : (fun r => hsq g a r * psiRe r)
      = fun r => hsq g a r * (psiRe r - psiRe 0) + psiRe 0 * hsq g a r := by
    funext r; ring
  rw [e, integral_add hi ((integrable_hsq hp ha).const_mul _), he, integral_const_mul,
    integral_hsq hp ha]
  field_simp
  ring

/-! ## B3. The bridge -/

/-- `WeilExplicit`'s first conjunct for `h = ĝ²`. -/
theorem hsq_ofReal (hp : Probe a g) (ha : 0 ≤ a) (r : ℝ) :
    ghatC g a r ^ 2 = ((hsq g a r : ℝ) : ℂ) := by
  rw [ghatC_real hp ha, hsq]; push_cast; rfl

/-- **The explicit-formula bridge**: for an even probe `g`, Weil's explicit formula for `h = ĝ²`
(and Gauss's digamma integral) gives `Σ_ρ ĝ(t_ρ)² = weilQ a g`. -/
theorem weilQ_eq_zero_sum {ι : Type*} {ρ : ι → ℂ} (hp : Probe a g) (ha : 0 < a)
    (hEF : WeilExplicit ρ (fun z => ghatC g a z ^ 2) (hsq g a)) (hD : DigammaDiff) :
    HasSum (fun i => ghatC g a ((ρ i - 1 / 2) / Complex.I) ^ 2) (weilQ a g : ℂ) := by
  obtain ⟨-, hS⟩ := hEF
  convert hS using 1
  have hpole1 : ghatC g a (Complex.I / 2) ^ 2 = ((poleR g a ^ 2 : ℝ) : ℂ) := by
    rw [ghatC_I_div_two]; push_cast; rfl
  have hpole2 : ghatC g a (-(Complex.I / 2)) ^ 2 = ((poleR g a ^ 2 : ℝ) : ℂ) := by
    rw [ghatC_even hp.even, hpole1]
  have hg0 : gh (hsq g a) 0 = normSq g := by rw [gh_hsq hp ha, autocorr_zero]
  have hpr : ∑' n : ℕ, ArithmeticFunction.vonMangoldt n / Real.sqrt n * gh (hsq g a) (Real.log n)
      = primeS g := by
    unfold primeS; congr 1; funext n; rw [gh_hsq hp ha]
  have hz0 : psiRe 0 = (Complex.digamma (1 / 4)).re := by unfold psiRe zB; simp
  simp only
  rw [hpole1, hpole2, hg0, hpr, arch_term hp ha hD, hz0, weilQ_eq', weilConst]
  push_cast; ring

/-- The same, as the zero-sum identity `weilQ a g = Σ_ρ ĝ(t_ρ)²`. -/
theorem weilQ_eq_tsum {ι : Type*} {ρ : ι → ℂ} (hp : Probe a g) (ha : 0 < a)
    (hEF : WeilExplicit ρ (fun z => ghatC g a z ^ 2) (hsq g a)) (hD : DigammaDiff) :
    (weilQ a g : ℂ) = ∑' i, ghatC g a ((ρ i - 1 / 2) / Complex.I) ^ 2 :=
  (weilQ_eq_zero_sum hp ha hEF hD).tsum_eq.symm

end Pilot1ca

#print axioms Pilot1ca.fourier_autocorr
#print axioms Pilot1ca.integrable_hsq
#print axioms Pilot1ca.gh_hsq
#print axioms Pilot1ca.integral_hsq
#print axioms Pilot1ca.psiRe_sub
#print axioms Pilot1ca.hsq_psi_sub
#print axioms Pilot1ca.arch_term
#print axioms Pilot1ca.hsq_ofReal
#print axioms Pilot1ca.weilQ_eq_zero_sum
#print axioms Pilot1ca.weilQ_eq_tsum
