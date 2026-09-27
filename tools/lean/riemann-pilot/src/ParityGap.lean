import Mathlib
import SwapRealize
import ParitySplit

/-! # Real zeros from the parity gap (round 137)

**Theorem A** (`realRooted_of_parityGap`). At support `a`, suppose the *parity gap*: every normalised odd probe
has `Q_g(o) > λ₁(a)`, the even ground energy (`ParityGap`). Then the transform of every even ground state has
only real zeros, in the whole complex plane. No simplicity of the ground state is assumed.

**Proof.** Take a non-real zero `w` of `ĝ`. Flip it with a real multiplier `m` such that `|m| = 1` on `ℝ` and
`m(z)m(−z) ≡ 1`:
* `m = (z − w̄)(z + w)/((z − w)(z + w̄))` if `Re w ≠ 0`, realised by `h = g + (4 Im w/Re w)·Re(w·k_{−w})` (`hR`);
* `m = (z − w̄)/(z − w)` if `w = iy`, realised by `h = g + 2y·Re k_{−w}` (`hI`).

Here `k_c(x) = ∫_{−a}^{x} g(y)e^{ic(x−y)} dy` is the first-order Green function (`kG`), which vanishes outside
`[−a, a]` because `ĝ(−c) = 0`, and has `k̂_c = iĝ/(z + c)` (`kG_hat`). The steps are:
1. `|ĥ| = |ĝ|` on `ℝ`, and `|ĝ|` on `ℝ` determines the autocorrelation for any real function (G1,
   `autocorr_eq_of_norm`: Fourier inversion without parity). So `h` has the same norm, archimedean term and
   prime term as `g`.
2. The pole product `ĥ(i/2)ĥ(−i/2)` is unchanged, so `Q_g(h) = Q(g) = λ₁`.
3. The parity split (`weilQg_parity`) writes `λ₁ = Q(e) + Q_g(o)`, and the gap forces `o = 0`
   (`swap_even_of_gap`). So `ĥ` is even.
4. Then `ĝ(r)(m(r) − m(−r)) = 0` on `ℝ`, with `m(r) ≠ m(−r)` off a finite set. So `ĝ = 0` a.e. on `ℝ`, and
   `‖g‖ = 0` (G5).

**Corollary** (`rh_of_parity_gap`). Ground states with the parity gap at all large supports, together with
`HypConv`, give `RiemannHypothesis`, through `rh_of_prime_side`. Eventual simplicity is no longer needed.

**Scope.** The parity gap `λ_even(a) < λ_odd(a)` for all large `a` is not proved. It is the whole remaining
content, and I know of no argument for it. This is a variant of the Carathéodory–Fejér / Connes–van Suijlekom
mechanism.
-/

open Real Filter Topology Complex MeasureTheory Set
open scoped FourierTransform

noncomputable section

namespace Pilot1ca

/-! ## G1. Fourier inversion for the autocorrelation of any real `L²` function on `[−a, a]` -/

/-- `g` is square-integrable and vanishes outside `[−a, a]` (no parity). -/
structure RSupp (a : ℝ) (g : ℝ → ℝ) : Prop where
  supp : ∀ u, a < |u| → g u = 0
  memL2 : MemLp g 2 volume

theorem RSupp.integrable {a : ℝ} {g : ℝ → ℝ} (hp : RSupp a g) : Integrable g := by
  have hfin : IsFiniteMeasure (volume.restrict (Icc (-a) a)) :=
    isFiniteMeasure_restrict.2 measure_Icc_lt_top.ne
  have h1 : IntegrableOn g (Icc (-a) a) := (hp.memL2.restrict _).integrable (by norm_num)
  refine (integrableOn_iff_integrable_of_support_subset fun u hu => ?_).1 h1
  rw [Function.mem_support] at hu
  have : |u| ≤ a := by
    by_contra h; push Not at h; exact hu (hp.supp u h)
  exact abs_le.1 this

/-- `conj ĝ(z) = ĝ(−z̄)` for every real `f`. -/
theorem ghatC_conj_neg {f : ℝ → ℝ} {a : ℝ} (ha : 0 ≤ a) (z : ℂ) :
    (starRingEnd ℂ) (ghatC f a z) = ghatC f a (-((starRingEnd ℂ) z)) := by
  unfold ghatC
  rw [intervalIntegral.integral_of_le (by linarith), intervalIntegral.integral_of_le (by linarith),
    ← integral_conj]
  congr 1; funext u
  rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, map_mul, map_mul, Complex.conj_I,
    Complex.conj_ofReal]
  congr 2; ring

theorem ghatC_neg_real {f : ℝ → ℝ} {a : ℝ} (ha : 0 ≤ a) (r : ℝ) :
    ghatC f a (-(r : ℂ)) = (starRingEnd ℂ) (ghatC f a r) := by
  rw [ghatC_conj_neg ha, Complex.conj_ofReal]

variable {a : ℝ} {g : ℝ → ℝ}

theorem autocorr_eq_conv_neg (g : ℝ → ℝ) (x : ℝ) :
    autocorr g x = ∫ s, g (-s) * g (x - s) := by
  unfold autocorr
  rw [← integral_neg_eq_self (fun t => g t * g (t + x))]
  congr 1; funext s; rw [show -s + x = x - s by ring]

/-- **The convolution identity, any parity**: `∫ f(x)e^{irx} dx = ĝ(r)ĝ(−r)`. -/
theorem fourier_autocorr_gen (hp : RSupp a g) (ha : 0 < a) (r : ℝ) :
    ∫ x, (autocorr g x : ℂ) * Complex.exp (Complex.I * r * x) = ghatC g a r * ghatC g a (-(r : ℂ)) := by
  have hg := hp.integrable
  have hgt : Integrable (fun s => g (-s)) := hg.comp_neg
  set e : ℝ → ℂ := fun x => Complex.exp (Complex.I * r * x) with he
  have he1 : ∀ x, ‖e x‖ = 1 := fun x => by
    simp only [he, Complex.norm_exp]
    have : (Complex.I * (r : ℂ) * (x : ℂ)).re = 0 := by simp
    rw [this, Real.exp_zero]
  have h0 := hgt.convolution_integrand (L := ContinuousLinearMap.mul ℝ ℝ) hg (μ := volume) (ν := volume)
  simp only [ContinuousLinearMap.mul_apply'] at h0
  have hF : Integrable (Function.uncurry fun x t : ℝ => ((g (-t) * g (x - t) : ℝ) : ℂ) * e x)
      (volume.prod volume) := by
    refine Integrable.mono' h0.norm
      ((Complex.continuous_ofReal.comp_aestronglyMeasurable h0.aestronglyMeasurable).mul
        ((by fun_prop : Continuous fun p : ℝ × ℝ => e p.1).aestronglyMeasurable)) ?_
    refine Eventually.of_forall fun p => ?_
    show ‖((g (-p.2) * g (p.1 - p.2) : ℝ) : ℂ) * e p.1‖ ≤ _
    rw [norm_mul, he1, mul_one, Complex.norm_real]
  have hinner : ∀ t, ∫ x, ((g (-t) * g (x - t) : ℝ) : ℂ) * e x = ((g (-t) : ℂ) * e t) * ghatC g a r := by
    intro t
    have e1 : (fun x => ((g (-t) * g (x - t) : ℝ) : ℂ) * e x)
        = fun x => ((g (-t) : ℂ) * e t) * (fun y => ((g y : ℝ) : ℂ) * e y) (x - t) := by
      funext x
      simp only [he]
      rw [show Complex.I * (r : ℂ) * (x : ℂ) = Complex.I * r * t + Complex.I * r * ((x - t : ℝ) : ℂ) by
        push_cast; ring, Complex.exp_add]
      push_cast; ring
    rw [e1, integral_const_mul, integral_sub_right_eq_self (fun y => ((g y : ℝ) : ℂ) * e y) t,
      ghatC_eq_integral ha hp.supp]
  have hneg : (∫ t, ((g (-t) : ℂ) * e t)) = ghatC g a (-(r : ℂ)) := by
    rw [ghatC_eq_integral ha hp.supp, ← integral_neg_eq_self]
    congr 1; funext t; simp only [he, neg_neg]; congr 1; push_cast; ring_nf
  calc ∫ x, (autocorr g x : ℂ) * e x
      = ∫ x, ∫ t, ((g (-t) * g (x - t) : ℝ) : ℂ) * e x := by
        congr 1; funext x
        rw [autocorr_eq_conv_neg, ← integral_complex_ofReal, ← integral_mul_const]
    _ = ∫ t, ∫ x, ((g (-t) * g (x - t) : ℝ) : ℂ) * e x := integral_integral_swap hF
    _ = ∫ t, ((g (-t) : ℂ) * e t) * ghatC g a r := by congr 1; funext t; exact hinner t
    _ = ghatC g a r * ghatC g a (-(r : ℂ)) := by rw [integral_mul_const, hneg, mul_comm]

/-- `|ĝ(r)|²` on the real line. -/
def gN (g : ℝ → ℝ) (a r : ℝ) : ℝ := ‖ghatC g a r‖ ^ 2

theorem gN_nonneg (r : ℝ) : 0 ≤ gN g a r := sq_nonneg _

theorem mul_neg_eq_gN (ha : 0 ≤ a) (r : ℝ) :
    ghatC g a r * ghatC g a (-(r : ℂ)) = (gN g a r : ℂ) := by
  rw [ghatC_neg_real ha, Complex.mul_conj, Complex.normSq_eq_norm_sq, gN]

theorem continuous_gN (hp : RSupp a g) : Continuous (gN g a) :=
  ((ghatC_differentiable (hp.integrable).intervalIntegrable).continuous.comp
    Complex.continuous_ofReal).norm.pow 2

theorem norm_ghatC_real_le (hp : RSupp a g) (ha : 0 < a) (r : ℝ) : ‖ghatC g a r‖ ≤ ∫ u, |g u| := by
  rw [ghatC_eq_integral ha hp.supp]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  congr 1; funext u
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]
  have : (Complex.I * (r : ℂ) * (u : ℂ)).re = 0 := by simp
  rw [this, Real.exp_zero, mul_one]

theorem integrable_autocorr_gen (hp : RSupp a g) (ha : 0 < a) : Integrable (autocorr g) := by
  refine (continuous_autocorr hp.memL2).integrable_of_hasCompactSupport ?_
  refine HasCompactSupport.intro (isCompact_Icc (a := -(2 * a)) (b := 2 * a)) fun u hu => ?_
  apply autocorr_eq_zero hp.supp
  simp only [mem_Icc, not_and_or, not_le] at hu
  rcases hu with h | h
  · rw [abs_of_neg (by linarith)]; linarith
  · rw [abs_of_pos (by linarith)]; exact h

/-- `|ĝ(2πξ)|²`: Mathlib's Fourier transform of `f`. -/
def PhiG (g : ℝ → ℝ) (a ξ : ℝ) : ℝ := gN g a (2 * π * ξ)

theorem fourier_autocorr_eq_gen (hp : RSupp a g) (ha : 0 < a) (ξ : ℝ) :
    𝓕 (fun x : ℝ => (autocorr g x : ℂ)) ξ = (PhiG g a ξ : ℂ) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  have e : (fun v : ℝ => Complex.exp (↑(-2 * π * v * ξ) * Complex.I) • (autocorr g v : ℂ))
      = fun v => (autocorr g v : ℂ) * Complex.exp (Complex.I * ((-(2 * π * ξ) : ℝ) : ℂ) * v) := by
    funext v; rw [smul_eq_mul, mul_comm]; congr 2; push_cast; ring
  rw [e, fourier_autocorr_gen hp ha, Complex.ofReal_neg, neg_neg, mul_comm, mul_neg_eq_gN ha.le, PhiG]

theorem tendsto_gauss_PhiG (hp : RSupp a g) (ha : 0 < a) :
    Tendsto (fun c : ℝ => ∫ x, Real.exp (-c⁻¹ * x ^ 2) * PhiG g a x) atTop (𝓝 (autocorr g 0)) := by
  set F : ℝ → ℂ := fun x => (autocorr g x : ℂ) with hF
  have hFi : Integrable F := (integrable_autocorr_gen hp ha).ofReal
  have hFc : Continuous F := Complex.continuous_ofReal.comp (continuous_autocorr hp.memL2)
  have hT := Real.tendsto_integral_gaussian_smul' hFi (v := (0 : ℝ)) hFc.continuousAt
  have key : ∀ c : ℝ, 0 < c →
      (∫ w : ℝ, ((π * c : ℂ) ^ (Module.finrank ℝ ℝ / 2 : ℂ)
          * cexp (-π ^ 2 * c * ‖(0 : ℝ) - w‖ ^ 2)) • F w)
        = ((∫ x, Real.exp (-c⁻¹ * x ^ 2) * PhiG g a x : ℝ) : ℂ) := by
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
    have hx : 𝓕 F x = (PhiG g a x : ℂ) := fourier_autocorr_eq_gen hp ha x
    have hx2 : ((‖x‖ : ℝ) : ℂ) ^ 2 = (x : ℂ) ^ 2 := by
      rw [← Complex.ofReal_pow, Real.norm_eq_abs, sq_abs, Complex.ofReal_pow]
    rw [hx, smul_eq_mul, Complex.ofReal_mul, Complex.ofReal_exp, hx2]
    push_cast; ring_nf
  have hT' : Tendsto (fun c : ℝ => ((∫ x, Real.exp (-c⁻¹ * x ^ 2) * PhiG g a x : ℝ) : ℂ)) atTop
      (𝓝 (F 0)) :=
    hT.congr' ((eventually_gt_atTop 0).mono fun c hc => key c hc)
  have := (Complex.continuous_re.tendsto _).comp hT'
  simpa [hF, Function.comp_def] using this

theorem PhiG_nonneg (x : ℝ) : 0 ≤ PhiG g a x := gN_nonneg _

theorem continuous_PhiG (hp : RSupp a g) : Continuous (PhiG g a) :=
  (continuous_gN hp).comp (continuous_const.mul continuous_id)

theorem PhiG_le (hp : RSupp a g) (ha : 0 < a) (x : ℝ) : PhiG g a x ≤ (∫ u, |g u|) ^ 2 := by
  unfold PhiG gN
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_ghatC_real_le hp ha _) 2

theorem integrable_PhiG (hp : RSupp a g) (ha : 0 < a) : Integrable (PhiG g a) := by
  set C := (∫ u, |g u|) ^ 2
  have hk : ∀ n : ℕ, Integrable (fun x => Real.exp (-((n : ℝ) + 1)⁻¹ * x ^ 2) * PhiG g a x) := by
    intro n
    refine (integrable_exp_neg_mul_sq (by positivity : (0 : ℝ) < ((n : ℝ) + 1)⁻¹)).mul_bdd
      (continuous_PhiG hp).aestronglyMeasurable (c := C) (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (PhiG_nonneg x)]; exact PhiG_le hp ha x
  have hkn : ∀ n : ℕ, ∀ x, 0 ≤ Real.exp (-((n : ℝ) + 1)⁻¹ * x ^ 2) * PhiG g a x :=
    fun n x => mul_nonneg (Real.exp_pos _).le (PhiG_nonneg x)
  have hlim : Tendsto (fun n : ℕ => ∫⁻ x, ENNReal.ofReal (Real.exp (-((n : ℝ) + 1)⁻¹ * x ^ 2)
      * PhiG g a x)) atTop (𝓝 (∫⁻ x, ENNReal.ofReal (PhiG g a x))) := by
    refine lintegral_tendsto_of_tendsto_of_monotone (fun n => ?_) ?_ ?_
    · exact ((Real.continuous_exp.comp (continuous_const.mul (continuous_pow 2))).mul
        (continuous_PhiG hp)).measurable.ennreal_ofReal.aemeasurable
    · refine Eventually.of_forall fun x => fun m n hmn => ENNReal.ofReal_le_ofReal ?_
      refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_) (PhiG_nonneg x)
      have h1 : ((n : ℝ) + 1)⁻¹ ≤ ((m : ℝ) + 1)⁻¹ :=
        inv_anti₀ (by positivity) (by exact_mod_cast Nat.add_le_add_right hmn 1)
      nlinarith [sq_nonneg x]
    · refine Eventually.of_forall fun x => ENNReal.tendsto_ofReal ?_
      have h0 : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat.congr fun n => by rw [one_div]
      have h1 : Tendsto (fun n : ℕ => -((n : ℝ) + 1)⁻¹ * x ^ 2) atTop (𝓝 0) := by
        simpa using h0.neg.mul_const (x ^ 2)
      have := ((Real.continuous_exp.tendsto 0).comp h1).mul_const (PhiG g a x)
      simpa using this
  have hval : Tendsto (fun n : ℕ => ∫⁻ x, ENNReal.ofReal (Real.exp (-((n : ℝ) + 1)⁻¹ * x ^ 2)
      * PhiG g a x)) atTop (𝓝 (ENNReal.ofReal (autocorr g 0))) := by
    have hc : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
    have := ENNReal.tendsto_ofReal ((tendsto_gauss_PhiG hp ha).comp hc)
    refine this.congr fun n => ?_
    simp only [Function.comp]
    exact ofReal_integral_eq_lintegral_ofReal (hk n) (Eventually.of_forall (hkn n))
  have heq := tendsto_nhds_unique hlim hval
  refine ⟨(continuous_PhiG hp).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall PhiG_nonneg), heq]
  exact ENNReal.ofReal_lt_top

/-- **Fourier inversion, any parity**: `f(u) = ∫ |ĝ(2πv)|² cos(2πvu) dv`. -/
theorem autocorr_eq_inv_gen (hp : RSupp a g) (ha : 0 < a) (u : ℝ) :
    autocorr g u = ∫ v, PhiG g a v * Real.cos (2 * π * v * u) := by
  set F : ℝ → ℂ := fun x => (autocorr g x : ℂ) with hF
  have hFi : Integrable F := (integrable_autocorr_gen hp ha).ofReal
  have hFc : Continuous F := Complex.continuous_ofReal.comp (continuous_autocorr hp.memL2)
  have hFF : 𝓕 F = fun ξ => (PhiG g a ξ : ℂ) := funext (fourier_autocorr_eq_gen hp ha)
  have hFFi : Integrable (𝓕 F) := by rw [hFF]; exact (integrable_PhiG hp ha).ofReal
  have h := congrFun (Continuous.fourierInv_fourier_eq hFc hFi hFFi) u
  rw [Real.fourierInv_eq', hFF] at h
  simp only [RCLike.inner_apply, conj_trivial] at h
  have hI : Integrable (fun v : ℝ => cexp (↑(2 * π * (u * v)) * I) • (PhiG g a v : ℂ)) := by
    refine (integrable_PhiG hp ha).ofReal.bdd_mul (c := 1)
      (by fun_prop : Continuous fun v : ℝ => cexp (↑(2 * π * (u * v)) * I)).aestronglyMeasurable
      (Eventually.of_forall fun v => ?_)
    rw [Complex.norm_exp_ofReal_mul_I]
  have hre := congrArg Complex.re h
  have hre2 : (∫ v : ℝ, cexp (↑(2 * π * (u * v)) * I) • (PhiG g a v : ℂ)).re
      = ∫ v : ℝ, (cexp (↑(2 * π * (u * v)) * I) • (PhiG g a v : ℂ)).re := (integral_re hI).symm
  rw [hre2] at hre
  simp only [hF, Complex.ofReal_re] at hre
  rw [← hre]
  congr 1; funext v
  rw [smul_eq_mul, mul_comm, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re,
    show 2 * π * (u * v) = 2 * π * v * u by ring]

/-- **`|ĝ|` on `ℝ` determines the autocorrelation** (any parity). -/
theorem autocorr_eq_of_norm {h : ℝ → ℝ} (hg : RSupp a g) (hh : RSupp a h) (ha : 0 < a)
    (heq : ∀ r : ℝ, ‖ghatC g a r‖ = ‖ghatC h a r‖) (u : ℝ) : autocorr g u = autocorr h u := by
  rw [autocorr_eq_inv_gen hg ha, autocorr_eq_inv_gen hh ha]
  congr 1; funext v; unfold PhiG gN; rw [heq]

/-! ## G2. The first-order Green function `k_c(x) = ∫_{−a}^{x} g(y) e^{ic(x−y)} dy` -/

theorem Pc_of_le {g : ℝ → ℝ} {a : ℝ} (hsupp : ∀ u, a < |u| → g u = 0) (c : ℂ) {x : ℝ} (hx : x ≤ -a) :
    Pc g a c x = 0 := by
  unfold Pc
  rw [intervalIntegral.integral_symm, intervalIntegral.integral_of_le hx, integral_Ioc_eq_integral_Ioo,
    setIntegral_eq_zero_of_forall_eq_zero, neg_zero]
  intro y hy
  rw [hsupp y (lt_of_lt_of_le (by linarith [hy.2]) (neg_le_abs y))]; simp

/-- `k_c(x) = e^{icx} P_{−c}(x)`. -/
def kG (g : ℝ → ℝ) (a : ℝ) (c : ℂ) (x : ℝ) : ℂ := Complex.exp (Complex.I * c * x) * Pc g a (-c) x

theorem kG_continuous {g : ℝ → ℝ} (hg : MemLp g 2 volume) (a : ℝ) (c : ℂ) : Continuous (kG g a c) := by
  have := Pc_continuous hg a (-c); unfold kG; fun_prop

theorem kG_supp {g : ℝ → ℝ} {a : ℝ} (hg : MemLp g 2 volume) (hsupp : ∀ u, a < |u| → g u = 0) {c : ℂ}
    (hc : ghatC g a (-c) = 0) (x : ℝ) (hx : a < |x|) : kG g a c x = 0 := by
  unfold kG
  rcases le_or_gt 0 x with h0 | h0
  · rw [abs_of_nonneg h0] at hx
    rw [Pc_of_ge hg hsupp _ hx.le, hc, mul_zero]
  · rw [abs_of_neg h0] at hx
    rw [Pc_of_le hsupp _ (by linarith), mul_zero]

theorem ii_conj (f : ℝ → ℂ) (α β : ℝ) :
    (starRingEnd ℂ) (∫ x in α..β, f x) = ∫ x in α..β, (starRingEnd ℂ) (f x) := by
  simp only [intervalIntegral, map_sub, integral_conj]

theorem Pc_conj {g : ℝ → ℝ} (a : ℝ) (c : ℂ) (x : ℝ) :
    (starRingEnd ℂ) (Pc g a c x) = Pc g a (-(starRingEnd ℂ) c) x := by
  unfold Pc
  rw [ii_conj]
  congr 1; funext y
  rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, map_mul, map_mul, Complex.conj_I,
    Complex.conj_ofReal]
  congr 2; ring

theorem kG_conj {g : ℝ → ℝ} (a : ℝ) (c : ℂ) (x : ℝ) :
    (starRingEnd ℂ) (kG g a c x) = kG g a (-(starRingEnd ℂ) c) x := by
  unfold kG
  rw [map_mul, ← Complex.exp_conj, map_mul, map_mul, Complex.conj_I, Complex.conj_ofReal, Pc_conj,
    map_neg, neg_neg]
  congr 2; ring

/-- **`k̂_c(z) = iĝ(z)/(z + c)`** when `ĝ(−c) = 0`. -/
theorem kG_hat {g : ℝ → ℝ} (hg : MemLp g 2 volume) {a : ℝ} (ha : 0 ≤ a) {c : ℂ}
    (hc : ghatC g a (-c) = 0) {z : ℂ} (hzc : z + c ≠ 0) :
    (∫ x in (-a)..a, kG g a c x * Complex.exp (Complex.I * z * x))
      = Complex.I * ghatC g a z / (z + c) := by
  have e : (fun x : ℝ => kG g a c x * Complex.exp (Complex.I * z * x))
      = fun x : ℝ => Complex.exp (Complex.I * (z + c) * x) * Pc g a (-c) x := by
    funext x; unfold kG
    rw [show Complex.I * (z + c) * x = Complex.I * c * x + Complex.I * z * x by ring, Complex.exp_add]
    ring
  rw [e, hat_exp_Pc hg ha c z hzc, hc, mul_zero, zero_sub]
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  field_simp
  rw [Complex.I_sq]; ring

/-! ## G3. The generic swap contradiction -/

theorem ghatC_neg_I_div_two (g : ℝ → ℝ) (a : ℝ) : ghatC g a (-(I / 2)) = (poleL g a : ℂ) := by
  unfold ghatC poleL
  rw [← intervalIntegral.integral_ofReal]
  apply intervalIntegral.integral_congr
  intro u _
  have e : I * -(I / 2) * (u : ℂ) = ((u / 2 : ℝ) : ℂ) := by
    push_cast
    linear_combination (-(u / 2) : ℂ) * I_mul_I
  simp only
  rw [e, ← ofReal_exp]
  push_cast
  ring

theorem ghatC_neg_of_ae_even {h : ℝ → ℝ} {a : ℝ} (hh : (fun t => h (-t)) =ᵐ[volume] h) (z : ℂ) :
    ghatC h a (-z) = ghatC h a z := by
  unfold ghatC
  have e1 := intervalIntegral.integral_comp_neg (a := -a) (b := a)
    (fun x : ℝ => ((h x : ℝ) : ℂ) * Complex.exp (Complex.I * (-z) * x))
  simp only [neg_neg] at e1
  rw [← e1]
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [hh] with x hx _
  simp only [hx]
  congr 2; push_cast; ring

/-- The parity gap at support `a`: every normalised odd probe has energy above the even ground energy. -/
def ParityGap (a : ℝ) : Prop := ∀ o, OProbe a o → normSq o = 1 → lam a < weilQg a o

theorem weilQ_eq_lam {a : ℝ} (ha : 0 < a) {g : ℝ → ℝ} (hg : IsGroundState a g) : weilQ a g = lam a := by
  have h1 := lam_mul_le hg.1
  rw [hg.2.1, mul_one] at h1
  have h2 : weilQ a g ≤ lam a :=
    le_csInf ⟨_, box a, box_probe a, normSq_box ha, rfl⟩ fun q ⟨h', hp', hn', hq⟩ => hq ▸ hg.2.2 h' hp' hn'
  linarith

/-- **The generic swap contradiction.** Let `g` be an even ground state and `h` a real function on
`[−a, a]` with `|ĥ| = |ĝ|` on `ℝ` and the same pole product `ĥ(i/2)ĥ(−i/2)`. Under the parity gap, `ĥ` is
even on the real line wherever `ĝ ≠ 0`, outside the exceptional set `{0} ∪ {r² = s}`, so `ĥ(r) = ĥ(−r)` there
is impossible to violate. -/
theorem swap_even_of_gap {a : ℝ} (ha : 0 < a) (hgap : ParityGap a) {g h : ℝ → ℝ}
    (hg : IsGroundState a g) (hh : RSupp a h)
    (hN : ∀ r : ℝ, ‖ghatC h a r‖ = ‖ghatC g a r‖)
    (hP : ghatC h a (I / 2) * ghatC h a (-(I / 2)) = ghatC g a (I / 2) * ghatC g a (-(I / 2))) (z : ℂ) :
    ghatC h a (-z) = ghatC h a z := by
  have hgR : RSupp a g := ⟨hg.1.supp, hg.1.memL2⟩
  have hA : ∀ u, autocorr h u = autocorr g u :=
    fun u => autocorr_eq_of_norm hh hgR ha (fun r => (hN r)) u
  have hAI : archIntegrand h = archIntegrand g := by
    funext u; unfold archIntegrand; rw [hA, hA]
  have hS : SProbe a h := ⟨hh.supp, hh.memL2, by rw [hAI]; exact hg.1.arch⟩
  have hn : normSq h = 1 := by rw [← autocorr_zero, hA, autocorr_zero, hg.2.1]
  have hpole : poleR h a * poleL h a = poleR g a * poleL g a := by
    have := hP
    rw [ghatC_I_div_two, ghatC_neg_I_div_two, ghatC_I_div_two, ghatC_neg_I_div_two] at this
    exact_mod_cast this
  have hQ : weilQg a h = weilQ a g := by
    rw [← weilQg_even hg.1]
    unfold weilQg
    have e1 : archE h = archE g := by unfold archE; rw [hAI]
    have e2 : primeS h = primeS g := by unfold primeS; simp only [hA]
    rw [e1, e2, hn, hg.2.1]; linarith [hpole]
  have hlam := weilQ_eq_lam ha hg
  -- the parity split
  rw [weilQg_parity hS] at hQ
  have hnp := normSq_parity hS.memL2
  rw [hn] at hnp
  have he := weilQ_ge_mul (c := lam a) ha (fun e hp hn1 => by rw [← hlam]; exact hg.2.2 e hp hn1) (probe_evenPart hS)
  have ho := oprobe_oddPart hS
  have ho0 : normSq (oddPart h) = 0 := by
    by_contra hne
    have hpos : 0 < normSq (oddPart h) := lt_of_le_of_ne (normSq_nonneg _) (Ne.symm hne)
    set k := 1 / Real.sqrt (normSq (oddPart h))
    have hk2 : k ^ 2 * normSq (oddPart h) = 1 := by
      simp only [k]; rw [div_pow, Real.sq_sqrt hpos.le]; field_simp
    have h1 := hgap _ (ho.smul k) (by rw [normSq_smul]; exact hk2)
    rw [weilQg_smul] at h1
    have hk0 : 0 < k ^ 2 := by positivity
    have h2 : lam a * normSq (oddPart h) < weilQg a (oddPart h) := by
      have : lam a * normSq (oddPart h) * k ^ 2 < weilQg a (oddPart h) * k ^ 2 := by
        rw [mul_assoc, mul_comm (normSq _), hk2, mul_one, mul_comm]; exact h1
      exact lt_of_mul_lt_mul_right this hk0.le
    rw [← hlam] at h2 he
    have hs : weilQ a g * (normSq (evenPart h) + normSq (oddPart h)) = weilQ a g := by rw [← hnp, mul_one]
    nlinarith
  have hz := ae_zero_of_normSq ho.memL2 ho0
  have hev : (fun t => h (-t)) =ᵐ[volume] h := by
    filter_upwards [hz] with t ht
    simp only [oddPart, Pi.zero_apply] at ht
    linarith
  exact ghatC_neg_of_ae_even hev z

/-! ## G4. The two real swaps -/

theorem ghatC_neg_conj_zero {g : ℝ → ℝ} {a : ℝ} (ha : 0 ≤ a) {w : ℂ} (hw : ghatC g a w = 0) :
    ghatC g a (-(starRingEnd ℂ) w) = 0 := by
  rw [← ghatC_conj_neg ha, hw, map_zero]

theorem memLp_real_part {k : ℝ → ℂ} (hk : Continuous k) {a : ℝ} (hs : ∀ x, a < |x| → k x = 0) (c : ℂ) :
    MemLp (fun x => (c * k x).re) 2 volume := by
  have hc : Continuous (fun x => (c * k x).re) := Complex.continuous_re.comp (continuous_const.mul hk)
  exact hc.memLp_of_hasCompactSupport (hasCompactSupport_of_supp (a := a) fun x hx => by
    simp [hs x hx])

theorem ii_kG_exp {g : ℝ → ℝ} (hg : MemLp g 2 volume) (a : ℝ) (c z : ℂ) (α β : ℝ) :
    IntervalIntegrable (fun x : ℝ => kG g a c x * Complex.exp (Complex.I * z * x)) volume α β :=
  (by have := kG_continuous hg a c; fun_prop : Continuous fun x : ℝ =>
    kG g a c x * Complex.exp (Complex.I * z * x)).intervalIntegrable _ _

/-- **The transform of `g + C·Re(c·k)`**: `ĝ + (C/2)(c k̂ + c̄ k̂*)`, `k* = conj k`. -/
theorem ghatC_add_re {g : ℝ → ℝ} (hg : MemLp g 2 volume) (a : ℝ) (C : ℝ) (c d : ℂ) (z : ℂ) :
    ghatC (fun x => g x + C * (c * kG g a d x).re) a z
      = ghatC g a z + (C : ℂ) / 2 * (c * (∫ x in (-a)..a, kG g a d x * Complex.exp (Complex.I * z * x))
        + (starRingEnd ℂ) c
          * (∫ x in (-a)..a, kG g a (-(starRingEnd ℂ) d) x * Complex.exp (Complex.I * z * x))) := by
  unfold ghatC
  have e : (fun x : ℝ => (((g x + C * (c * kG g a d x).re : ℝ) : ℂ)) * Complex.exp (Complex.I * z * x))
      = fun x => ((g x : ℝ) : ℂ) * Complex.exp (Complex.I * z * x)
        + ((C : ℂ) / 2 * c) * (kG g a d x * Complex.exp (Complex.I * z * x))
        + ((C : ℂ) / 2 * (starRingEnd ℂ) c)
          * (kG g a (-(starRingEnd ℂ) d) x * Complex.exp (Complex.I * z * x)) := by
    funext x
    rw [← kG_conj]
    have hre : (((c * kG g a d x).re : ℝ) : ℂ) = (c * kG g a d x + (starRingEnd ℂ) (c * kG g a d x)) / 2 :=
      Complex.re_eq_add_conj _
    push_cast
    rw [hre, map_mul]
    ring
  rw [e, intervalIntegral.integral_add ((ii_mul_exp hg z _ _).add ((ii_kG_exp hg a d z _ _).const_mul _))
      ((ii_kG_exp hg a _ z _ _).const_mul _),
    intervalIntegral.integral_add (ii_mul_exp hg z _ _) ((ii_kG_exp hg a d z _ _).const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  ring

section caseR

variable {g : ℝ → ℝ} {a : ℝ} {w : ℂ}

/-- The swap for a zero `w` off the imaginary axis: `h = g + (4 Im w/Re w)·Re(w·k_{−w})`. -/
def hR (g : ℝ → ℝ) (a : ℝ) (w : ℂ) (x : ℝ) : ℝ := g x + 4 * w.im / w.re * (w * kG g a (-w) x).re

/-- `m(z) = (z − w̄)(z + w)/((z − w)(z + w̄))`. -/
def mR (w z : ℂ) : ℂ := (z - (starRingEnd ℂ) w) * (z + w) / ((z - w) * (z + (starRingEnd ℂ) w))

theorem hR_rsupp (hp : Probe a g) (hw : ghatC g a w = 0) : RSupp a (hR g a w) := by
  have hc : ghatC g a (-(-w)) = 0 := by rw [neg_neg]; exact hw
  refine ⟨fun x hx => ?_, hp.memL2.add ((memLp_real_part (kG_continuous hp.memL2 a (-w))
    (kG_supp hp.memL2 hp.supp hc) w).const_mul _)⟩
  simp only [hR, hp.supp x hx, kG_supp hp.memL2 hp.supp hc x hx, mul_zero, Complex.zero_re, zero_add]

theorem hR_hat (hp : Probe a g) (ha : 0 ≤ a) (hw : ghatC g a w = 0) (hre : w.re ≠ 0) {z : ℂ}
    (h1 : z - w ≠ 0) (h2 : z + (starRingEnd ℂ) w ≠ 0) :
    ghatC (hR g a w) a z = ghatC g a z * mR w z := by
  have hc1 : ghatC g a (-(-w)) = 0 := by rw [neg_neg]; exact hw
  have hc2 : ghatC g a (-(-(starRingEnd ℂ) (-w))) = 0 := by
    rw [map_neg, neg_neg]; exact ghatC_neg_conj_zero ha hw
  have e := ghatC_add_re hp.memL2 a (4 * w.im / w.re) w (-w) z
  have hk1 := kG_hat hp.memL2 ha hc1 (z := z) (by rw [← sub_eq_add_neg]; exact h1)
  have hk2 := kG_hat hp.memL2 ha hc2 (z := z) (by rw [map_neg, neg_neg]; exact h2)
  rw [map_neg, neg_neg] at hk2
  unfold hR
  rw [map_neg, neg_neg] at e
  rw [e, hk1, hk2, mR]
  have hwre : (w.re : ℂ) = (w + (starRingEnd ℂ) w) / 2 := Complex.re_eq_add_conj w
  have hwim : (w.im : ℂ) = (w - (starRingEnd ℂ) w) / (2 * Complex.I) := Complex.im_eq_sub_conj w
  have hs : w + (starRingEnd ℂ) w ≠ 0 := by
    intro h0; apply hre; have := congrArg Complex.re h0; simp at this; linarith
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  have h1' : z + -w ≠ 0 := by rwa [← sub_eq_add_neg]
  push_cast
  rw [hwre, hwim]
  field_simp
  ring

end caseR

section caseI

variable {g : ℝ → ℝ} {a : ℝ} {w : ℂ}

/-- The swap for a zero `w = iy` on the imaginary axis: `h = g + 2y·Re k_{−w}`. -/
def hI (g : ℝ → ℝ) (a : ℝ) (w : ℂ) (x : ℝ) : ℝ := g x + 2 * w.im * (1 * kG g a (-w) x).re

/-- `m(z) = (z − w̄)/(z − w)`. -/
def mI (w z : ℂ) : ℂ := (z - (starRingEnd ℂ) w) / (z - w)

theorem conj_of_re_zero (hre : w.re = 0) : (starRingEnd ℂ) w = -w := by
  apply Complex.ext <;> simp [hre]

theorem hI_rsupp (hp : Probe a g) (hw : ghatC g a w = 0) : RSupp a (hI g a w) := by
  have hc : ghatC g a (-(-w)) = 0 := by rw [neg_neg]; exact hw
  refine ⟨fun x hx => ?_, hp.memL2.add ((memLp_real_part (kG_continuous hp.memL2 a (-w))
    (kG_supp hp.memL2 hp.supp hc) 1).const_mul _)⟩
  simp only [hI, hp.supp x hx, kG_supp hp.memL2 hp.supp hc x hx, mul_zero, Complex.zero_re, zero_add]

theorem hI_hat (hp : Probe a g) (ha : 0 ≤ a) (hw : ghatC g a w = 0) (hre : w.re = 0) {z : ℂ}
    (h1 : z - w ≠ 0) : ghatC (hI g a w) a z = ghatC g a z * mI w z := by
  have hcw := conj_of_re_zero hre
  have hc1 : ghatC g a (-(-w)) = 0 := by rw [neg_neg]; exact hw
  have e := ghatC_add_re hp.memL2 a (2 * w.im) 1 (-w) z
  rw [map_neg, neg_neg, hcw, map_one] at e
  have hk1 := kG_hat hp.memL2 ha hc1 (z := z) (by rw [← sub_eq_add_neg]; exact h1)
  unfold hI
  rw [e, hk1, mI, hcw]
  have hwim : (w.im : ℂ) = (w - (starRingEnd ℂ) w) / (2 * Complex.I) := Complex.im_eq_sub_conj w
  rw [hcw] at hwim
  have hI0 : Complex.I ≠ 0 := Complex.I_ne_zero
  have h1' : z + -w ≠ 0 := by rwa [← sub_eq_add_neg]
  push_cast
  rw [hwim]
  field_simp
  ring

end caseI

/-! ## G5. Real zeros from the parity gap -/

theorem normSq_zero_of_ghat_zero {a : ℝ} {g : ℝ → ℝ} (hp : RSupp a g) (ha : 0 < a) (s : ℝ)
    (h0 : ∀ r : ℝ, r ≠ 0 → r ^ 2 ≠ s → ghatC g a r = 0) : normSq g = 0 := by
  have hinv := autocorr_eq_inv_gen hp ha 0
  rw [autocorr_zero] at hinv
  rw [hinv]
  set F : Set ℝ := {0, Real.sqrt s / (2 * π), -(Real.sqrt s / (2 * π))}
  have hF : volume F = 0 := (Set.toFinite F).measure_zero volume
  refine integral_eq_zero_of_ae ?_
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hF] with v hv
  simp only [Pi.zero_apply]
  have hπ : (0 : ℝ) < 2 * π := by positivity
  have hv0 : 2 * π * v ≠ 0 := by
    intro h; apply hv; left; rcases mul_eq_zero.1 h with h | h
    · exact absurd h hπ.ne'
    · exact h
  have hvs : (2 * π * v) ^ 2 ≠ s := by
    intro h
    apply hv
    have hs : 0 ≤ s := h ▸ sq_nonneg _
    have habs : |2 * π * v| = Real.sqrt s := by rw [← h, Real.sqrt_sq_eq_abs]
    rcases abs_eq (Real.sqrt_nonneg s) |>.1 habs with h' | h'
    · right; left; rw [eq_div_iff hπ.ne']; linarith
    · right; right; simp only [Set.mem_singleton_iff]; rw [← neg_div, eq_div_iff hπ.ne']; linarith
  rw [PhiG, gN, h0 _ hv0 hvs, norm_zero]; simp

/-- From the evenness of `ĥ` and `ĥ = ĝ·m` on `ℝ`: `ĝ(r) = 0` wherever `m(r) ≠ m(−r)`. -/
theorem ghat_zero_of_sym {a : ℝ} {g h : ℝ → ℝ} (hge : ∀ z, ghatC g a (-z) = ghatC g a z) {m : ℂ → ℂ}
    (hm : ∀ r : ℝ, ghatC h a r = ghatC g a r * m r) (hsym : ∀ z, ghatC h a (-z) = ghatC h a z)
    {r : ℝ} (hr : m r ≠ m (-(r : ℂ))) : ghatC g a r = 0 := by
  have e1 := hsym r
  have e2 := hm (-r)
  push_cast at e2
  rw [e2, hm r, hge] at e1
  have : ghatC g a r * (m r - m (-(r : ℂ))) = 0 := by linear_combination -e1
  rcases mul_eq_zero.1 this with h | h
  · exact h
  · exact absurd (sub_eq_zero.1 h) hr

theorem real_sub_ne {w : ℂ} (him : w.im ≠ 0) (r : ℝ) : (r : ℂ) - w ≠ 0 := by
  intro h; apply him; have := congrArg Complex.im h; simpa using this
theorem real_add_ne {w : ℂ} (him : w.im ≠ 0) (r : ℝ) : (r : ℂ) + w ≠ 0 := by
  intro h; apply him; have := congrArg Complex.im h; simp at this; linarith
theorem real_sub_conj_ne {w : ℂ} (him : w.im ≠ 0) (r : ℝ) : (r : ℂ) - (starRingEnd ℂ) w ≠ 0 := by
  intro h; apply him; have := congrArg Complex.im h; simp at this; linarith
theorem real_add_conj_ne {w : ℂ} (him : w.im ≠ 0) (r : ℝ) : (r : ℂ) + (starRingEnd ℂ) w ≠ 0 := by
  intro h; apply him; have := congrArg Complex.im h; simpa using this

theorem norm_real_sub_conj {w : ℂ} (r : ℝ) : ‖(r : ℂ) - (starRingEnd ℂ) w‖ = ‖(r : ℂ) - w‖ := by
  rw [← Complex.norm_conj, map_sub, Complex.conj_ofReal, Complex.conj_conj]
theorem norm_real_add_conj {w : ℂ} (r : ℝ) : ‖(r : ℂ) + (starRingEnd ℂ) w‖ = ‖(r : ℂ) + w‖ := by
  rw [← Complex.norm_conj, map_add, Complex.conj_ofReal, Complex.conj_conj]

/-- **Theorem A.** Under the parity gap, the transform of every even ground state has only real zeros
(in the whole plane). -/
theorem realRooted_of_parityGap {a : ℝ} (ha : 0 < a) (hgap : ParityGap a) {g : ℝ → ℝ}
    (hg : IsGroundState a g) : RealRooted a g := by
  intro w hw
  by_contra him
  have hp := hg.1
  have hge : ∀ z, ghatC g a (-z) = ghatC g a z := fun z => ghatC_even hp.even a z
  have hgR : RSupp a g := ⟨hp.supp, hp.memL2⟩
  have hn0 : normSq g ≠ 0 := by rw [hg.2.1]; exact one_ne_zero
  apply hn0
  by_cases hre : w.re = 0
  · -- the imaginary axis
    have hcw := conj_of_re_zero hre
    have hw0 : w ≠ 0 := fun h => him (by rw [h]; simp)
    have hm : ∀ r : ℝ, ghatC (hI g a w) a r = ghatC g a r * mI w r :=
      fun r => hI_hat hp ha.le hw hre (real_sub_ne him r)
    have hN : ∀ r : ℝ, ‖ghatC (hI g a w) a r‖ = ‖ghatC g a r‖ := by
      intro r
      rw [hm, norm_mul, mI, norm_div, norm_real_sub_conj, div_self (norm_ne_zero_iff.2 (real_sub_ne him r)),
        mul_one]
    have hP : ghatC (hI g a w) a (I / 2) * ghatC (hI g a w) a (-(I / 2))
        = ghatC g a (I / 2) * ghatC g a (-(I / 2)) := by
      by_cases hw1 : w = I / 2
      · have h2 : ghatC g a (-(I / 2)) = 0 := by rw [hge, ← hw1]; exact hw
        have h3 : ghatC (hI g a w) a (-(I / 2)) = 0 := by
          rw [hI_hat hp ha.le hw hre (by rw [hw1]; intro h; have := congrArg Complex.im h; norm_num at this),
            h2, zero_mul]
        rw [h3, h2, mul_zero, mul_zero]
      by_cases hw2 : w = -(I / 2)
      · have h2 : ghatC g a (I / 2) = 0 := by rw [← hge, ← hw2]; exact hw
        have h3 : ghatC (hI g a w) a (I / 2) = 0 := by
          rw [hI_hat hp ha.le hw hre (by rw [hw2]; intro h; have := congrArg Complex.im h; norm_num at this),
            h2, zero_mul]
        rw [h3, h2, zero_mul, zero_mul]
      have d1 : I / 2 - w ≠ 0 := fun h => hw1 (sub_eq_zero.1 h).symm
      have d2 : -(I / 2) - w ≠ 0 := fun h => hw2 (sub_eq_zero.1 h).symm
      rw [hI_hat hp ha.le hw hre d1, hI_hat hp ha.le hw hre d2]
      have hmm : mI w (I / 2) * mI w (-(I / 2)) = 1 := by
        unfold mI; rw [hcw, div_mul_div_comm, div_eq_one_iff_eq (mul_ne_zero d1 d2)]
        ring
      linear_combination (ghatC g a (I / 2) * ghatC g a (-(I / 2))) * hmm
    have hsym := swap_even_of_gap ha hgap hg (hI_rsupp hp hw) hN hP
    refine normSq_zero_of_ghat_zero hgR ha 0 fun r hr0 _ => ?_
    refine ghat_zero_of_sym hge hm hsym ?_
    intro heq
    unfold mI at heq
    rw [hcw] at heq
    have d1 := real_sub_ne him r
    have d2 : -(r : ℂ) - w ≠ 0 := by
      have := real_add_ne him r; intro h; apply this; linear_combination -h
    rw [div_eq_div_iff d1 d2] at heq
    have : 4 * (r : ℂ) * w = 0 := by linear_combination -heq
    rcases mul_eq_zero.1 this with h | h
    · rcases mul_eq_zero.1 h with h | h
      · norm_num at h
      · exact hr0 (by exact_mod_cast h)
    · exact hw0 h
  · -- off both axes (and off the imaginary axis): the pair swap
    have hm : ∀ r : ℝ, ghatC (hR g a w) a r = ghatC g a r * mR w r :=
      fun r => hR_hat hp ha.le hw hre (real_sub_ne him r) (real_add_conj_ne him r)
    have hN : ∀ r : ℝ, ‖ghatC (hR g a w) a r‖ = ‖ghatC g a r‖ := by
      intro r
      rw [hm, norm_mul, mR, norm_div, norm_mul, norm_mul, norm_real_sub_conj, ← norm_real_add_conj (w := w) r,
        div_self (mul_ne_zero (norm_ne_zero_iff.2 (real_sub_ne him r))
          (norm_ne_zero_iff.2 (real_add_conj_ne him r))), mul_one]
    have hre' : ∀ c : ℂ, c.re = 0 → c - w ≠ 0 ∧ c + (starRingEnd ℂ) w ≠ 0 := by
      intro c hc
      constructor
      · intro h; apply hre; have := congrArg Complex.re h; simp [hc] at this; linarith
      · intro h; apply hre; have := congrArg Complex.re h; simp [hc] at this; linarith
    have hP : ghatC (hR g a w) a (I / 2) * ghatC (hR g a w) a (-(I / 2))
        = ghatC g a (I / 2) * ghatC g a (-(I / 2)) := by
      obtain ⟨d1, d2⟩ := hre' (I / 2) (by simp)
      obtain ⟨d3, d4⟩ := hre' (-(I / 2)) (by simp)
      rw [hR_hat hp ha.le hw hre d1 d2, hR_hat hp ha.le hw hre d3 d4]
      have hmm : mR w (I / 2) * mR w (-(I / 2)) = 1 := by
        unfold mR
        rw [div_mul_div_comm, div_eq_one_iff_eq (mul_ne_zero (mul_ne_zero d1 d2) (mul_ne_zero d3 d4))]
        ring
      linear_combination (ghatC g a (I / 2) * ghatC g a (-(I / 2))) * hmm
    have hsym := swap_even_of_gap ha hgap hg (hR_rsupp hp hw) hN hP
    refine normSq_zero_of_ghat_zero hgR ha (‖w‖ ^ 2) fun r hr0 hrs => ?_
    refine ghat_zero_of_sym hge hm hsym ?_
    intro heq
    unfold mR at heq
    have d1 := real_sub_ne him r
    have d2 := real_add_conj_ne him r
    have d3 : -(r : ℂ) - w ≠ 0 := by
      have := real_add_ne him r; intro h; apply this; linear_combination -h
    have d4 : -(r : ℂ) + (starRingEnd ℂ) w ≠ 0 := by
      have := real_sub_conj_ne him r; intro h; apply this; linear_combination -h
    rw [div_eq_div_iff (mul_ne_zero d1 d2) (mul_ne_zero d3 d4)] at heq
    have hww : w * (starRingEnd ℂ) w = ((‖w‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    have hkey : 4 * (w - (starRingEnd ℂ) w) * (r : ℂ) * ((r : ℂ) ^ 2 - w * (starRingEnd ℂ) w) = 0 := by
      linear_combination heq
    rw [hww] at hkey
    have hwc : w - (starRingEnd ℂ) w ≠ 0 := by
      intro h; apply him; have := congrArg Complex.im h; simp at this; linarith
    have hr2 : (r : ℂ) ^ 2 - ((‖w‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
      intro h; apply hrs; exact_mod_cast sub_eq_zero.1 h
    have hr0' : (r : ℂ) ≠ 0 := by exact_mod_cast hr0
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (4 : ℂ) ≠ 0) hwc) hr0') hr2 hkey

/-- **RH from the parity gap.** Ground states with the parity gap at every large support, and
convergence of their transforms to `Ξ` (`HypConv`), give Mathlib's `RiemannHypothesis`; no simplicity. -/
theorem rh_of_parity_gap {a : ℕ → ℝ} {g : ℕ → ℝ → ℝ} (ha : ∀ n, 0 < a n)
    (hgs : ∀ n, IsGroundState (a n) (g n)) (hgap : ∀ᶠ n in atTop, ParityGap (a n))
    (hconv : HypConv a g) : RiemannHypothesis :=
  rh_of_prime_side hgs (hgap.mono fun n h => realRooted_of_parityGap (ha n) h (hgs n)) hconv

end Pilot1ca

#print axioms Pilot1ca.autocorr_eq_of_norm
#print axioms Pilot1ca.kG_hat
#print axioms Pilot1ca.swap_even_of_gap
#print axioms Pilot1ca.hR_hat
#print axioms Pilot1ca.hI_hat
#print axioms Pilot1ca.realRooted_of_parityGap
#print axioms Pilot1ca.rh_of_parity_gap
