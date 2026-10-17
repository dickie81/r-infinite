import Mathlib

/-! # The Bessel function `K_ν` (round 361)

S5f-1 of round 360's plan, part 2. `K_ν(x) = ½∫_0^∞ t^{ν−1}e^{−x(t+1/t)/2} dt`, defined as half the
Mellin transform of the kernel `t ↦ e^{−x(t+1/t)/2}` (Mathlib's `mellin`), so that Mathlib's Mellin
API applies. Mathlib's `Analysis/SpecialFunctions/Bessel.lean` has only the first kind.

* **Convergence** (`mellinConvergent_bkK`): for `x > 0` the Mellin integral converges at every
  `ν ∈ ℂ`, since the kernel decays like `e^{−xt/2}` at `∞` and like `e^{−x/(2t)}` at `0`.
* **The bound by the real case** (`norm_besselK_le`): `|K_ν(x)| ≤ ½∫_0^∞ t^{Re ν−1}e^{−x(t+1/t)/2} dt`.
* **Decay** (`bkR_le_exp`): for `0 < x₀ ≤ x`, `∫_0^∞ t^{r−1}e^{−x(t+1/t)/2} dt ≤
  e^{−x/2}∫_0^∞ t^{r−1}e^{−x₀(t+1/t)/4} dt`, from `t + 1/t ≥ 2`.
-/

open Real Set Filter Asymptotics MeasureTheory
open scoped Topology

noncomputable section

namespace Eis

/-- The kernel `t ↦ e^{−x(t + 1/t)/2}` of `K_ν(x)`. -/
def bkK (x t : ℝ) : ℝ := Real.exp (-(x / 2) * (t + t⁻¹))

/-- **The Bessel function of the second kind**, `K_ν(x) = ½∫_0^∞ t^{ν−1}e^{−x(t + 1/t)/2} dt`: half the
Mellin transform of the kernel at `ν`. -/
def besselK (ν : ℂ) (x : ℝ) : ℂ := (1 / 2 : ℂ) * mellin (fun t => (bkK x t : ℂ)) ν

/-- The real majorant `∫_0^∞ t^{r−1}e^{−x(t + 1/t)/2} dt = 2K_r(x)`. -/
def bkR (r x : ℝ) : ℝ := ∫ t in Ioi (0 : ℝ), t ^ (r - 1) * bkK x t

theorem bkK_pos (x t : ℝ) : 0 < bkK x t := Real.exp_pos _

theorem bkK_continuousOn (x : ℝ) : ContinuousOn (bkK x) (Ioi 0) := by
  unfold bkK
  refine Real.continuous_exp.comp_continuousOn ?_
  exact continuousOn_const.mul (continuousOn_id.add (continuousOn_inv₀.mono fun t ht => ne_of_gt ht))

theorem bkK_le_top {x : ℝ} (hx : 0 < x) {t : ℝ} (ht : 0 < t) : bkK x t ≤ Real.exp (-(x / 2) * t) := by
  unfold bkK; apply Real.exp_le_exp.2
  have : 0 < t⁻¹ := inv_pos.2 ht
  nlinarith

theorem bkK_le_bot {x : ℝ} (hx : 0 < x) {t : ℝ} (ht : 0 < t) : bkK x t ≤ Real.exp (-(x / 2) * t⁻¹) := by
  unfold bkK; apply Real.exp_le_exp.2
  nlinarith

theorem locInt_bkK (x : ℝ) : LocallyIntegrableOn (fun t => (bkK x t : ℂ)) (Ioi 0) :=
  (Complex.continuous_ofReal.comp_continuousOn (bkK_continuousOn x)).locallyIntegrableOn
    measurableSet_Ioi

/-- **The Mellin integral of the kernel converges at every `ν`** when `x > 0`: the kernel decays like
`e^{−xt/2}` at `∞` and like `e^{−x/(2t)}` at `0`. -/
theorem mellinConvergent_bkK {x : ℝ} (hx : 0 < x) (ν : ℂ) :
    MellinConvergent (fun t => (bkK x t : ℂ)) ν := by
  have hx2 : 0 < x / 2 := by positivity
  refine mellinConvergent_of_isBigO_rpow_exp hx2 (locInt_bkK x) ?_ ?_ (b := ν.re - 1) (by linarith)
  · refine IsBigO.of_bound 1 ?_
    filter_upwards [eventually_gt_atTop 0] with t ht
    rw [Complex.norm_real, Real.norm_of_nonneg (bkK_pos x t).le, one_mul,
      Real.norm_of_nonneg (Real.exp_pos _).le]
    exact bkK_le_top hx ht
  · have h1 := (isLittleO_exp_neg_mul_rpow_atTop hx2 (ν.re - 1)).comp_tendsto tendsto_inv_nhdsGT_zero
    have h2 : ((fun x : ℝ => x ^ (ν.re - 1)) ∘ fun t : ℝ => t⁻¹) =ᶠ[𝓝[>] 0]
        fun t => t ^ (-(ν.re - 1)) := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      simp only [Function.comp_apply]
      rw [Real.inv_rpow (le_of_lt ht), Real.rpow_neg (le_of_lt ht)]
    refine IsBigO.trans ?_ (h1.isBigO.congr' EventuallyEq.rfl h2)
    refine IsBigO.of_bound 1 ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [Complex.norm_real, Real.norm_of_nonneg (bkK_pos x t).le, one_mul, Function.comp_apply,
      Real.norm_of_nonneg (Real.exp_pos _).le]
    exact bkK_le_bot hx ht

theorem integrableOn_bkR {x : ℝ} (hx : 0 < x) (r : ℝ) :
    IntegrableOn (fun t : ℝ => t ^ (r - 1) * bkK x t) (Ioi 0) := by
  have h := mellinConvergent_bkK hx (r : ℂ)
  rw [MellinConvergent, mellin_convergent_iff_norm Subset.rfl measurableSet_Ioi
    (locInt_bkK x).aestronglyMeasurable] at h
  refine h.congr_fun (fun t ht => ?_) measurableSet_Ioi
  simp only [Complex.ofReal_re, Complex.norm_real, Real.norm_of_nonneg (bkK_pos x t).le]

theorem bkR_nonneg (r x : ℝ) : 0 ≤ bkR r x :=
  setIntegral_nonneg measurableSet_Ioi fun t ht => mul_nonneg (Real.rpow_nonneg (le_of_lt ht) _)
    (bkK_pos x t).le

/-- `|K_ν(x)| ≤ ½∫_0^∞ t^{Re ν − 1}e^{−x(t + 1/t)/2} dt`. -/
theorem norm_besselK_le (ν : ℂ) (x : ℝ) : ‖besselK ν x‖ ≤ (1 / 2) * bkR ν.re x := by
  unfold besselK mellin bkR
  rw [norm_mul, show ‖(1 / 2 : ℂ)‖ = 1 / 2 by norm_num]
  gcongr
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht, Complex.norm_real,
    Real.norm_of_nonneg (bkK_pos x t).le]
  simp

/-- `e^{−x(t+1/t)/2} ≤ e^{−x/2}·e^{−(x/2)(t+1/t)/2}`, since `t + 1/t ≥ 2`. -/
theorem bkK_le_half {x : ℝ} (hx : 0 ≤ x) {t : ℝ} (ht : 0 < t) :
    bkK x t ≤ Real.exp (-(x / 2)) * bkK (x / 2) t := by
  unfold bkK
  rw [← Real.exp_add]
  apply Real.exp_le_exp.2
  have h2 : 2 ≤ t + t⁻¹ := by
    have : 0 < t⁻¹ := inv_pos.2 ht
    have h1 : t * t⁻¹ = 1 := mul_inv_cancel₀ ht.ne'
    nlinarith [sq_nonneg (t - t⁻¹)]
  nlinarith

theorem bkK_anti {x y : ℝ} (hxy : x ≤ y) {t : ℝ} (ht : 0 < t) : bkK y t ≤ bkK x t := by
  unfold bkK
  apply Real.exp_le_exp.2
  have : 0 < t + t⁻¹ := by have := inv_pos.2 ht; linarith
  nlinarith

/-- **Decay**: `∫ t^{r−1}e^{−x(t+1/t)/2} ≤ e^{−x/2}·∫ t^{r−1}e^{−x₀(t+1/t)/4}` for `0 < x₀ ≤ x`. -/
theorem bkR_le_exp {r x₀ x : ℝ} (hx₀ : 0 < x₀) (hx : x₀ ≤ x) :
    bkR r x ≤ Real.exp (-(x / 2)) * bkR r (x₀ / 2) := by
  have hx0 : 0 < x := hx₀.trans_le hx
  unfold bkR
  rw [← integral_const_mul]
  refine setIntegral_mono_on (integrableOn_bkR hx0 r)
    ((integrableOn_bkR (by positivity) r).const_mul _) measurableSet_Ioi fun t ht => ?_
  have hp : 0 ≤ t ^ (r - 1) := Real.rpow_nonneg (le_of_lt ht) _
  calc t ^ (r - 1) * bkK x t ≤ t ^ (r - 1) * (Real.exp (-(x / 2)) * bkK (x / 2) t) :=
        mul_le_mul_of_nonneg_left (bkK_le_half hx0.le ht) hp
    _ ≤ t ^ (r - 1) * (Real.exp (-(x / 2)) * bkK (x₀ / 2) t) := by
        gcongr
        exact bkK_anti (by linarith) ht
    _ = Real.exp (-(x / 2)) * (t ^ (r - 1) * bkK (x₀ / 2) t) := by ring

end Eis

end

#print axioms Eis.bkK_pos
#print axioms Eis.bkK_continuousOn
#print axioms Eis.bkK_le_top
#print axioms Eis.bkK_le_bot
#print axioms Eis.locInt_bkK
#print axioms Eis.mellinConvergent_bkK
#print axioms Eis.integrableOn_bkR
#print axioms Eis.bkR_nonneg
#print axioms Eis.norm_besselK_le
#print axioms Eis.bkK_le_half
#print axioms Eis.bkK_anti
#print axioms Eis.bkR_le_exp
