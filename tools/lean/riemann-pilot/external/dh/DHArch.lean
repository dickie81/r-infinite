import Mathlib
import DHPacket

/-! # The archimedean term of the packet, bounded (round 260, certificate stage 2)

The Weil form of `dh` on the packet (`QDHu_packet_eq`, round 259) has the archimedean term
`E_{3/4}(g) = ∫_0^∞ [f(0) − f(u)] K(u) du`, `K(u) = e^{−u/2}/sinh u`, which for a wave packet is large
(`≈ 4.83‖g‖²` at the target) and must be evaluated, not bounded crudely. This file proves

`Re ψ(¾)·‖g‖² + E_{3/4}(g) ≤ ‖g‖²·[log √(9/16 + ω²/4) + 3/ω] + ‖g‖²·(4/3)e^{−3a}/(1 − e^{−4a}) + 1/(2ω) + (1 + log 2aω)/(2ω)`

(`packet_arch_total_le`, for `0 < a`, `0 < ω`, `2aω ≥ 1`), in which `ψ(¾)` has cancelled and every remaining
number is elementary. Its ingredients:

**Two Frullani integrals** (`integral_one_sub_cos_mul_exp_div`: `∫_0^∞ (1 − cos bt) e^{−ct}/t dt = ½ log(1 + b²/c²)`;
`integral_exp_sub_exp_div`: `∫_0^∞ (e^{−ct} − e^{−dt})/t dt = log(d/c)`), the real parts of round 155's complex
Frullani integral `PilotDigamma.integral_frullani`.
**The Gauss kernel split.** `e^{−3t/4}/(1 − e^{−t}) = e^{−3t/4}/t + h(t)` with `h(t) = e^{−3t/4}φ₂(t)`,
`φ₂(t) = 1/(1 − e^{−t}) − 1/t ∈ [½, 1]` increasing (`one_half_le_phi2`, `phi2_le_one`, `deriv_phi2_nonneg`);
integration by parts on `(0, ∞)` gives `|∫_0^∞ h(t) cos(ct) dt| ≤ (3/2)/c` (`abs_integral_hK_cos_le`, with
`∫|h′| ≤ 3/2`).
**Binet at `¾`.** `∫_0^∞ e^{−t}φ₂(t) dt = γ` (`integral_exp_mul_phi2_eq_eulerMascheroni`: the truncations
`∫ (1 − e^{−nt}) e^{−t}φ₂` are `H_n − log(n + 1) = eulerMascheroniSeq n`, and monotone convergence meets
Mathlib's `tendsto_eulerMascheroniSeq`), hence `∫_0^∞ h = log ¾ − ψ(¾)` (`integral_hK_eq`, through Gauss's
difference formula of round 154 at `z = ¾`, `w = 1`, and `digamma_one`).
**The split Gauss integral** (`psiReQ_three_quarters_sub`, `psiReQ_three_quarters_le`):
`Re ψ(¾ + iω/2) = log √(9/16 + ω²/4) − ∫_0^∞ h(t) cos(ωt/2) dt ≤ log √(9/16 + ω²/4) + 3/ω`.
**The kernel `K`** (`K_le_inv`: `K(u) ≤ 1/u`; `integral_K_tail_le`: `∫_{2a}^∞ K ≤ (4/3)e^{−3a}/(1 − e^{−4a})`;
`uK/2` at most `½` and non-increasing, so `|∫_0^{2a} (u/2)K cos ωu| ≤ 1/(2ω)`, `abs_integral_uK_cos_le`;
`|∫_0^{2a} K sin ωu| ≤ 1 + log 2aω`, `abs_integral_K_sin_le`).
**The assembly** (`packet_archEQ_le`): on `(0, 2a]` the closed form of `f` gives
`f(0) − f(u) = f(0)(1 − cos ωu) + (u/2) cos ωu + β sin ωu`, `β = cos(2ωa)/(2ω)`; beyond `2a`, `f = 0`; the
`(1 − cos)` pieces recombine to `f(0)·[Re ψ(¾ + iω/2) − ψ(¾)]` by the substitution `t = 2u` in Gauss's integral
(`psiReQ_three_quarters_sub_u`), and the three remainders are the bounds above.

The Frullani, `h`, Binet, `K` and assembly sections were built by agents to stated interfaces and re-read and
recompiled by the lead; the split Gauss integral and its `u`-form are the lead's.
-/

open Real Complex MeasureTheory Set Filter Topology

noncomputable section

namespace PsiOmega

open LandauLaplace Pilot1ca Pilot1bt PilotWeil

/-! ## Two Frullani integrals -/

/-- Pointwise: the real part of the complex Frullani integrand at `w = c`, `z = c + ib`. -/
theorem frullani_re_cos (b c t : ℝ) :
    RCLike.re ((Complex.exp (-((c : ℂ) * t)) - Complex.exp (-(((c : ℂ) + b * Complex.I) * t))) / t)
      = (1 - Real.cos (b * t)) * Real.exp (-(c * t)) / t := by
  rw [RCLike.re_to_complex, Complex.div_ofReal_re, Complex.sub_re, Complex.exp_re, Complex.exp_re]
  simp [Complex.mul_re, Complex.mul_im]
  ring

/-- Pointwise: the real part of the complex Frullani integrand at `w = c`, `z = d`. -/
theorem frullani_re_exp (c d t : ℝ) :
    RCLike.re ((Complex.exp (-((c : ℂ) * t)) - Complex.exp (-((d : ℂ) * t))) / t)
      = (Real.exp (-(c * t)) - Real.exp (-(d * t))) / t := by
  rw [RCLike.re_to_complex, Complex.div_ofReal_re, Complex.sub_re, Complex.exp_re, Complex.exp_re]
  simp [Complex.mul_re, Complex.mul_im]

/-- `∫_0^∞ (1 − cos(bt)) e^{−ct}/t dt` converges absolutely for `c > 0`. -/
theorem integrableOn_one_sub_cos_mul_exp_div {b c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun t : ℝ => (1 - Real.cos (b * t)) * Real.exp (-(c * t)) / t) (Ioi 0) := by
  have hz : 0 < ((c : ℂ) + b * Complex.I).re := by simpa using hc
  have hw : 0 < (c : ℂ).re := by simpa using hc
  exact IntegrableOn.congr_fun (Integrable.re (PilotDigamma.integrableOn_frullani hz hw))
    (fun t _ => frullani_re_cos b c t) measurableSet_Ioi

/-- `∫_0^∞ (1 − cos(bt)) e^{−ct}/t dt = ½ log(1 + b²/c²)` for `c > 0`. -/
theorem integral_one_sub_cos_mul_exp_div {b c : ℝ} (hc : 0 < c) :
    ∫ t in Ioi (0 : ℝ), (1 - Real.cos (b * t)) * Real.exp (-(c * t)) / t
      = Real.log (1 + b ^ 2 / c ^ 2) / 2 := by
  have hz : 0 < ((c : ℂ) + b * Complex.I).re := by simpa using hc
  have hw : 0 < (c : ℂ).re := by simpa using hc
  rw [← setIntegral_congr_fun measurableSet_Ioi (fun t _ => frullani_re_cos b c t),
    integral_re (PilotDigamma.integrableOn_frullani hz hw), PilotDigamma.integral_frullani hz hw,
    RCLike.re_to_complex, Complex.sub_re, Complex.log_re, Complex.log_re, Complex.norm_add_mul_I,
    Complex.norm_real, Real.norm_of_nonneg hc.le]
  have hc2 : (0 : ℝ) < c ^ 2 := by positivity
  have hcb : (0 : ℝ) < c ^ 2 + b ^ 2 := by positivity
  rw [show 1 + b ^ 2 / c ^ 2 = (c ^ 2 + b ^ 2) / c ^ 2 by field_simp,
    Real.log_div hcb.ne' hc2.ne', Real.log_sqrt hcb.le, Real.log_pow]
  push_cast
  ring

/-- `∫_0^∞ (e^{−ct} − e^{−dt})/t dt` converges absolutely for `c, d > 0`. -/
theorem integrableOn_exp_sub_exp_div {c d : ℝ} (hc : 0 < c) (hd : 0 < d) :
    IntegrableOn (fun t : ℝ => (Real.exp (-(c * t)) - Real.exp (-(d * t))) / t) (Ioi 0) := by
  have hz : 0 < (d : ℂ).re := by simpa using hd
  have hw : 0 < (c : ℂ).re := by simpa using hc
  exact IntegrableOn.congr_fun (Integrable.re (PilotDigamma.integrableOn_frullani hz hw))
    (fun t _ => frullani_re_exp c d t) measurableSet_Ioi

/-- **Frullani**: `∫_0^∞ (e^{−ct} − e^{−dt})/t dt = log(d/c)` for `c, d > 0`. -/
theorem integral_exp_sub_exp_div {c d : ℝ} (hc : 0 < c) (hd : 0 < d) :
    ∫ t in Ioi (0 : ℝ), (Real.exp (-(c * t)) - Real.exp (-(d * t))) / t = Real.log (d / c) := by
  have hz : 0 < (d : ℂ).re := by simpa using hd
  have hw : 0 < (c : ℂ).re := by simpa using hc
  rw [← setIntegral_congr_fun measurableSet_Ioi (fun t _ => frullani_re_exp c d t),
    integral_re (PilotDigamma.integrableOn_frullani hz hw), PilotDigamma.integral_frullani hz hw,
    RCLike.re_to_complex, Complex.sub_re, ← Complex.ofReal_log hd.le, ← Complex.ofReal_log hc.le,
    Complex.ofReal_re, Complex.ofReal_re, Real.log_div hd.ne' hc.ne']

/-! ## The smooth part `h` of the Gauss kernel and its oscillatory integral -/

/-- `φ₂(t) = 1/(1 − e^{−t}) − 1/t`. -/
def phi2 (t : ℝ) : ℝ := 1 / (1 - Real.exp (-t)) - 1 / t
/-- `h(t) = e^{−3t/4} φ₂(t)`. -/
def hK (t : ℝ) : ℝ := Real.exp (-(3 / 4 * t)) * phi2 t

/-- `φ₂'(t) = 1/t² − e^{−t}/(1 − e^{−t})²`. -/
def dphi2 (t : ℝ) : ℝ := 1 / t ^ 2 - Real.exp (-t) / (1 - Real.exp (-t)) ^ 2

/-- `h'(t) = −¾ e^{−3t/4} φ₂(t) + e^{−3t/4} φ₂'(t)`. -/
def dhK (t : ℝ) : ℝ :=
  Real.exp (-(3 / 4 * t)) * (-(3 / 4)) * phi2 t + Real.exp (-(3 / 4 * t)) * dphi2 t

theorem kH_exp_neg_lt_one {t : ℝ} (ht : 0 < t) : Real.exp (-t) < 1 := by
  rw [← Real.exp_zero]; exact Real.exp_lt_exp.2 (by linarith)

theorem kH_one_sub_exp_neg_pos {t : ℝ} (ht : 0 < t) : 0 < 1 - Real.exp (-t) := by
  linarith [kH_exp_neg_lt_one ht]

/-- `e^{−t}(1 + t) ≤ 1`. -/
theorem kH_exp_neg_mul_one_add_le (t : ℝ) : Real.exp (-t) * (1 + t) ≤ 1 := by
  have h1 : Real.exp (-t) * Real.exp t = 1 := by rw [← Real.exp_add]; simp
  have h2 : t + 1 ≤ Real.exp t := Real.add_one_le_exp t
  nlinarith [Real.exp_pos (-t)]

/-- A function vanishing at `0`, continuous, with nonnegative derivative on `(0, ∞)`, is
nonnegative on `[0, ∞)`. -/
theorem kH_nonneg_of_hasDerivAt_nonneg {f f' : ℝ → ℝ} (hf : Continuous f) (h0 : f 0 = 0)
    (hd : ∀ x, 0 < x → HasDerivAt f (f' x) x) (hp : ∀ x, 0 < x → 0 ≤ f' x) {t : ℝ}
    (ht : 0 ≤ t) : 0 ≤ f t := by
  have hm : MonotoneOn f (Ici 0) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0) hf.continuousOn
      (fun x hx => by rw [interior_Ici] at hx ⊢; exact (hd x hx).hasDerivWithinAt)
      (fun x hx => by rw [interior_Ici] at hx; exact hp x hx)
  have := hm self_mem_Ici ht ht
  rwa [h0] at this

theorem kkQ_three_quarters_eq {t : ℝ} (ht : 0 < t) :
    kkQ (3 / 4) t = Real.exp (-(3 / 4 * t)) / t + hK t := by
  have hD := (kH_one_sub_exp_neg_pos ht).ne'
  have ht' := ht.ne'
  unfold kkQ hK phi2
  field_simp
  ring

theorem phi2_pos {t : ℝ} (ht : 0 < t) : 0 < phi2 t := by
  have hE : 1 - t < Real.exp (-t) := by
    linarith [Real.add_one_lt_exp (show -t ≠ 0 by linarith)]
  have hD := kH_one_sub_exp_neg_pos ht
  unfold phi2
  rw [sub_pos]
  exact one_div_lt_one_div_of_lt hD (by linarith)

theorem phi2_le_one {t : ℝ} (ht : 0 < t) : phi2 t ≤ 1 := by
  have hD := kH_one_sub_exp_neg_pos ht
  have hk := kH_exp_neg_mul_one_add_le t
  unfold phi2
  rw [div_sub_div _ _ hD.ne' ht.ne', div_le_one (by positivity)]
  nlinarith

theorem one_half_le_phi2 {t : ℝ} (ht : 0 < t) : 1 / 2 ≤ phi2 t := by
  have hD := kH_one_sub_exp_neg_pos ht
  have key : 0 ≤ t * (1 + Real.exp (-t)) - 2 * (1 - Real.exp (-t)) := by
    refine kH_nonneg_of_hasDerivAt_nonneg (f := fun t => t * (1 + Real.exp (-t)) - 2 * (1 - Real.exp (-t)))
      (f' := fun x => 1 - Real.exp (-x) * (1 + x)) (by fun_prop) (by simp) (fun x _ => ?_)
      (fun x _ => by linarith [kH_exp_neg_mul_one_add_le x]) ht.le
    have he : HasDerivAt (fun t : ℝ => Real.exp (-t)) (-Real.exp (-x)) x := by
      simpa using (hasDerivAt_neg x).exp
    exact (((hasDerivAt_id' x).mul (he.const_add 1)).sub ((he.const_sub 1).const_mul 2)).congr_deriv
      (by ring)
  unfold phi2
  rw [div_sub_div _ _ hD.ne' ht.ne', le_div_iff₀ (by positivity)]
  nlinarith

theorem hasDerivAt_phi2 {t : ℝ} (ht : 0 < t) :
    HasDerivAt phi2 (1 / t ^ 2 - Real.exp (-t) / (1 - Real.exp (-t)) ^ 2) t := by
  have hD := kH_one_sub_exp_neg_pos ht
  have he : HasDerivAt (fun t : ℝ => 1 - Real.exp (-t)) (Real.exp (-t)) t := by
    simpa using ((hasDerivAt_neg t).exp).const_sub 1
  have h1 := (hasDerivAt_const t (1 : ℝ)).div he hD.ne'
  have h2 := (hasDerivAt_const t (1 : ℝ)).div (hasDerivAt_id' t) ht.ne'
  exact (h1.sub h2).congr_deriv (by ring)

theorem deriv_phi2_nonneg {t : ℝ} (ht : 0 < t) :
    0 ≤ 1 / t ^ 2 - Real.exp (-t) / (1 - Real.exp (-t)) ^ 2 := by
  have hD := kH_one_sub_exp_neg_pos ht
  have hab : Real.exp (-(t / 2)) * Real.exp (t / 2) = 1 := by rw [← Real.exp_add]; simp
  have hE : Real.exp (-t) = Real.exp (-(t / 2)) * Real.exp (-(t / 2)) := by
    rw [← Real.exp_add]; congr 1; ring
  have hs : t / 2 ≤ Real.sinh (t / 2) := Real.self_le_sinh_iff.2 (by linarith)
  rw [Real.sinh_eq] at hs
  have ha : 0 < Real.exp (-(t / 2)) := Real.exp_pos _
  have hDa : Real.exp (-(t / 2)) * t ≤ 1 - Real.exp (-t) := by rw [hE]; nlinarith
  have hat : 0 ≤ Real.exp (-(t / 2)) * t := by positivity
  rw [sub_nonneg, div_le_div_iff₀ (by positivity) (by positivity)]
  have := mul_le_mul hDa hDa hat hD.le
  rw [hE] at this ⊢
  nlinarith

theorem hK_nonneg {t : ℝ} (ht : 0 < t) : 0 ≤ hK t :=
  mul_nonneg (Real.exp_pos _).le (phi2_pos ht).le

theorem hK_le {t : ℝ} (ht : 0 < t) : hK t ≤ Real.exp (-(3 / 4 * t)) := by
  unfold hK
  have := phi2_le_one ht
  have := Real.exp_pos (-(3 / 4 * t))
  nlinarith

theorem measurable_hK : Measurable hK := by unfold hK phi2; fun_prop

theorem measurable_dhK : Measurable dhK := by unfold dhK phi2 dphi2; fun_prop

theorem integrableOn_hK : IntegrableOn hK (Ioi 0) := by
  refine Integrable.mono' (integrableOn_exp_mul_Ioi (a := -(3 / 4)) (by norm_num) 0)
    measurable_hK.aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t (ht : 0 < t) => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (hK_nonneg ht), neg_mul]
  exact hK_le ht

/-! ## The limits of `φ₂` -/

theorem phi2_le_half_add {t : ℝ} (ht : 0 < t) : phi2 t ≤ 1 / 2 + t / 2 := by
  have hD := kH_one_sub_exp_neg_pos ht
  have hQ := Real.quadratic_le_exp_of_nonneg ht.le
  have h1 : Real.exp (-t) * Real.exp t = 1 := by rw [← Real.exp_add]; simp
  have hE := Real.exp_pos (-t)
  have hq : Real.exp (-t) * (1 + t + t ^ 2 / 2) ≤ 1 := by nlinarith
  have hl : 1 - t ≤ Real.exp (-t) := by linarith [Real.add_one_le_exp (-t)]
  have h2 : (1 - t) * t ≤ Real.exp (-t) * t := mul_le_mul_of_nonneg_right hl ht.le
  unfold phi2
  rw [div_sub_div _ _ hD.ne' ht.ne', div_le_iff₀ (by positivity)]
  nlinarith

theorem tendsto_phi2_zero : Tendsto phi2 (𝓝[>] 0) (𝓝 (1 / 2)) := by
  have hu : Tendsto (fun t : ℝ => 1 / 2 + t / 2) (𝓝[>] 0) (𝓝 (1 / 2)) := by
    have : Tendsto (fun t : ℝ => 1 / 2 + t / 2) (𝓝 0) (𝓝 (1 / 2 + 0 / 2)) :=
      tendsto_const_nhds.add (tendsto_id.div_const 2)
    rw [zero_div, add_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    exact one_half_le_phi2 ht
  · filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    exact phi2_le_half_add ht

theorem tendsto_phi2_atTop : Tendsto phi2 atTop (𝓝 1) := by
  have h1 : Tendsto (fun t : ℝ => 1 / (1 - Real.exp (-t))) atTop (𝓝 (1 / (1 - 0))) :=
    tendsto_const_nhds.div (tendsto_const_nhds.sub Real.tendsto_exp_neg_atTop_nhds_zero)
      (by norm_num)
  have h2 : Tendsto (fun t : ℝ => 1 / t) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
  have := h1.sub h2
  rw [sub_zero, sub_zero, div_one] at this
  exact this

/-- The continuous extension of `φ₂` to `0`. -/
def phi2e : ℝ → ℝ := Function.update phi2 0 (1 / 2)

theorem continuousWithinAt_phi2e : ContinuousWithinAt phi2e (Ici 0) 0 := by
  have h := tendsto_phi2_zero
  rw [← Ici_sdiff_left] at h
  exact continuousWithinAt_update_same.mpr h

theorem hasDerivAt_phi2e {x : ℝ} (hx : 0 < x) : HasDerivAt phi2e (dphi2 x) x := by
  apply (hasDerivAt_phi2 hx).congr_of_eventuallyEq
  filter_upwards [eventually_ne_nhds hx.ne'] with y hy
  exact Function.update_of_ne hy _ _

theorem tendsto_phi2e_atTop : Tendsto phi2e atTop (𝓝 1) := by
  apply tendsto_phi2_atTop.congr'
  filter_upwards [eventually_ne_atTop 0] with x hx
  exact (Function.update_of_ne hx _ _).symm

theorem integrableOn_dphi2 : IntegrableOn dphi2 (Ioi 0) :=
  integrableOn_Ioi_deriv_of_nonneg continuousWithinAt_phi2e (fun _ hx => hasDerivAt_phi2e hx)
    (fun _ hx => deriv_phi2_nonneg hx) tendsto_phi2e_atTop

theorem integral_dphi2 : ∫ t in Ioi (0 : ℝ), dphi2 t = 1 / 2 := by
  rw [integral_Ioi_of_hasDerivAt_of_nonneg continuousWithinAt_phi2e
    (fun _ hx => hasDerivAt_phi2e hx) (fun _ hx => deriv_phi2_nonneg hx) tendsto_phi2e_atTop]
  simp [phi2e]
  norm_num

/-! ## The oscillatory integral -/

theorem hasDerivAt_hK {x : ℝ} (hx : 0 < x) : HasDerivAt hK (dhK x) x := by
  have h1 : HasDerivAt (fun t : ℝ => -(3 / 4 * t)) (-(3 / 4)) x :=
    (((hasDerivAt_id' x).const_mul (3 / 4 : ℝ)).neg).congr_deriv (by ring)
  exact h1.exp.mul (hasDerivAt_phi2 hx)

theorem abs_dhK_le {t : ℝ} (ht : 0 < t) :
    |dhK t| ≤ dphi2 t + 3 / 4 * Real.exp (-(3 / 4) * t) := by
  have he := Real.exp_pos (-(3 / 4 * t))
  have he1 : Real.exp (-(3 / 4 * t)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
  have hp0 := (phi2_pos ht).le
  have hp1 := phi2_le_one ht
  have hd0 : 0 ≤ dphi2 t := deriv_phi2_nonneg ht
  have k1 : Real.exp (-(3 / 4 * t)) * phi2 t ≤ Real.exp (-(3 / 4 * t)) := by nlinarith
  have k2 : 0 ≤ Real.exp (-(3 / 4 * t)) * phi2 t := by positivity
  have k3 : Real.exp (-(3 / 4 * t)) * dphi2 t ≤ dphi2 t := by nlinarith
  have k4 : 0 ≤ Real.exp (-(3 / 4 * t)) * dphi2 t := by positivity
  rw [neg_mul]
  unfold dhK
  rw [abs_le]
  constructor <;> nlinarith

theorem norm_dhK_sin_le {c : ℝ} (hc : 0 < c) {t : ℝ} (ht : 0 < t) :
    ‖dhK t * (Real.sin (c * t) / c)‖ ≤ (dphi2 t + 3 / 4 * Real.exp (-(3 / 4) * t)) / c := by
  rw [Real.norm_eq_abs, abs_mul, abs_div, abs_of_pos hc]
  calc |dhK t| * (|Real.sin (c * t)| / c) ≤ |dhK t| * (1 / c) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (Real.abs_sin_le_one _) hc.le)
          (abs_nonneg _)
    _ = |dhK t| / c := by ring
    _ ≤ _ := div_le_div_of_nonneg_right (abs_dhK_le ht) hc.le

/-- **The oscillatory integral of `h` is `O(1/c)`**: `|∫_0^∞ h(t) cos(ct) dt| ≤ (3/2)/c`. -/
theorem abs_integral_hK_cos_le {c : ℝ} (hc : 0 < c) :
    |∫ t in Ioi (0 : ℝ), hK t * Real.cos (c * t)| ≤ 3 / 2 / c := by
  have hexp : IntegrableOn (fun t : ℝ => Real.exp (-(3 / 4) * t)) (Ioi 0) :=
    integrableOn_exp_mul_Ioi (by norm_num) 0
  have hB : IntegrableOn (fun t => (dphi2 t + 3 / 4 * Real.exp (-(3 / 4) * t)) / c) (Ioi 0) :=
    (integrableOn_dphi2.add (hexp.const_mul (3 / 4))).div_const c
  have hv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt (fun t => Real.sin (c * t) / c) (Real.cos (c * x)) x := by
    intro x _
    have := hc.ne'
    exact ((((hasDerivAt_id' x).const_mul c).sin).div_const c).congr_deriv (by field_simp)
  have huv : IntegrableOn (hK * fun t => Real.cos (c * t)) (Ioi 0) := by
    refine Integrable.mono' hexp (measurable_hK.mul (by fun_prop)).aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t (ht : 0 < t) => ?_)
    rw [Pi.mul_apply, Real.norm_eq_abs, abs_mul, abs_of_nonneg (hK_nonneg ht), neg_mul]
    calc hK t * |Real.cos (c * t)| ≤ hK t * 1 :=
          mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (hK_nonneg ht)
      _ ≤ _ := by rw [mul_one]; exact hK_le ht
  have hu'v : IntegrableOn (dhK * fun t => Real.sin (c * t) / c) (Ioi 0) := by
    refine Integrable.mono' hB (measurable_dhK.mul (by fun_prop)).aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t (ht : 0 < t) => ?_)
    exact norm_dhK_sin_le hc ht
  have h0 : Tendsto (hK * fun t => Real.sin (c * t) / c) (𝓝[>] 0) (𝓝 0) := by
    have hs : Tendsto (fun t : ℝ => |Real.sin (c * t) / c|) (𝓝[>] 0) (𝓝 0) := by
      have hcont : Continuous (fun t : ℝ => |Real.sin (c * t) / c|) := by fun_prop
      convert (hcont.tendsto 0).mono_left nhdsWithin_le_nhds using 2
      simp
    refine squeeze_zero_norm' ?_ hs
    filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    have hk1 : hK t ≤ 1 := (hK_le ht).trans (Real.exp_le_one_iff.2 (by nlinarith))
    rw [Pi.mul_apply, Real.norm_eq_abs, abs_mul, abs_of_nonneg (hK_nonneg ht)]
    calc hK t * |Real.sin (c * t) / c| ≤ 1 * |Real.sin (c * t) / c| :=
          mul_le_mul_of_nonneg_right hk1 (abs_nonneg _)
      _ = _ := one_mul _
  have hinf : Tendsto (hK * fun t => Real.sin (c * t) / c) atTop (𝓝 0) := by
    have ha : Tendsto (fun t : ℝ => Real.exp (-(3 / 4 * t)) / c) atTop (𝓝 0) := by
      have h1 : Tendsto (fun t : ℝ => 3 / 4 * t) atTop atTop :=
        tendsto_id.const_mul_atTop (by norm_num)
      have h2 := (Real.tendsto_exp_neg_atTop_nhds_zero.comp h1).div_const c
      rw [zero_div] at h2
      exact h2
    refine squeeze_zero_norm' ?_ ha
    filter_upwards [eventually_gt_atTop 0] with t ht
    rw [Pi.mul_apply, Real.norm_eq_abs, abs_mul, abs_of_nonneg (hK_nonneg ht), abs_div,
      abs_of_pos hc]
    calc hK t * (|Real.sin (c * t)| / c) ≤ Real.exp (-(3 / 4 * t)) * (1 / c) :=
          mul_le_mul (hK_le ht) (div_le_div_of_nonneg_right (Real.abs_sin_le_one _) hc.le)
            (by positivity) (Real.exp_pos _).le
      _ = _ := by ring
  have hibp := integral_Ioi_mul_deriv_eq_deriv_mul (u := hK) (u' := dhK)
    (v := fun t => Real.sin (c * t) / c) (v' := fun t => Real.cos (c * t))
    (fun x hx => hasDerivAt_hK hx) hv huv hu'v h0 hinf
  rw [hibp, sub_self, zero_sub, abs_neg, ← Real.norm_eq_abs]
  calc ‖∫ x in Ioi (0 : ℝ), dhK x * (Real.sin (c * x) / c)‖
      ≤ ∫ t in Ioi (0 : ℝ), (dphi2 t + 3 / 4 * Real.exp (-(3 / 4) * t)) / c := by
        refine norm_integral_le_of_norm_le hB ?_
        refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t (ht : 0 < t) => ?_)
        exact norm_dhK_sin_le hc ht
    _ = ((∫ t in Ioi (0 : ℝ), dphi2 t)
          + 3 / 4 * ∫ t in Ioi (0 : ℝ), Real.exp (-(3 / 4) * t)) / c := by
        rw [integral_div, integral_add integrableOn_dphi2 (hexp.const_mul (3 / 4)),
          integral_const_mul]
    _ = 3 / 2 / c := by
        rw [integral_dphi2, integral_exp_mul_Ioi (by norm_num) 0]
        norm_num

/-! ## The Euler–Mascheroni integral and Binet at `¾` -/

/-- `φ₂(t) = 1/(1 − e^{−t}) − 1/t` is measurable. -/
theorem measurable_phi2 : Measurable phi2 :=
  (measurable_const.div (measurable_const.sub (Real.measurable_exp.comp measurable_neg))).sub
    (measurable_const.div measurable_id)

theorem bq_integrableOn_exp {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun t : ℝ => Real.exp (-(c * t))) (Ioi 0) := by
  simpa [neg_mul] using exp_neg_integrableOn_Ioi 0 hc

theorem bq_integral_exp {c : ℝ} (hc : 0 < c) :
    ∫ t in Ioi (0 : ℝ), Real.exp (-(c * t)) = 1 / c := by
  have := integral_exp_mul_Ioi (a := -c) (by linarith) 0
  simp only [mul_zero, Real.exp_zero, neg_mul] at this
  rw [this, neg_div_neg_eq]

/-- `e^{−ct} φ₂(t)` is integrable on `(0, ∞)` for `c > 0` (it lies between `0` and `e^{−ct}`). -/
theorem integrableOn_exp_mul_phi2 {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun t => Real.exp (-(c * t)) * phi2 t) (Ioi 0) := by
  refine (bq_integrableOn_exp hc).mono'
    ((Real.measurable_exp.comp (measurable_const.mul measurable_id).neg).mul
      measurable_phi2).aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (phi2_pos ht).le)]
  exact mul_le_of_le_one_right (Real.exp_pos _).le (phi2_le_one ht)

/-- **Frullani for exponentials**, by Fubini: for `0 < a ≤ b`,
`∫_0^∞ (e^{−at} − e^{−bt})/t dt = log (b/a)`, with the integrand integrable. -/
theorem bq_frullani {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntegrableOn (fun t : ℝ => (Real.exp (-(a * t)) - Real.exp (-(b * t))) / t) (Ioi 0) ∧
      ∫ t in Ioi (0 : ℝ), (Real.exp (-(a * t)) - Real.exp (-(b * t))) / t = Real.log (b / a) := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hrep : EqOn (fun t : ℝ => (Real.exp (-(a * t)) - Real.exp (-(b * t))) / t)
      (fun t => ∫ s in Ioc a b, Real.exp (-(s * t))) (Ioi 0) := by
    intro t ht
    have htne : t ≠ 0 := (ne_of_gt ht)
    simp only
    rw [← intervalIntegral.integral_of_le hab]
    have hd : ∀ s ∈ uIcc a b, HasDerivAt (fun s => Real.exp (-(s * t)) / (-t))
        (Real.exp (-(s * t))) s := by
      intro s _
      have h := (((hasDerivAt_id' s).mul_const t).neg.exp).div_const (-t)
      convert h using 1
      simp only [Pi.neg_apply, one_mul]
      field_simp
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
      ((by fun_prop : Continuous fun s : ℝ => Real.exp (-(s * t))).intervalIntegrable a b)]
    field_simp
    ring
  let f : ℝ → ℝ → ℝ := fun s t => Real.exp (-(s * t))
  have hmeas : AEStronglyMeasurable (Function.uncurry f)
      ((volume.restrict (Ioc a b)).prod (volume.restrict (Ioi (0 : ℝ)))) :=
    (show Continuous fun p : ℝ × ℝ => Real.exp (-(p.1 * p.2)) by fun_prop).aestronglyMeasurable
  have hinner : ∀ s : ℝ, 0 < s → ∫ t in Ioi (0 : ℝ), ‖f s t‖ = s⁻¹ := by
    intro s hs
    simp only [f, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    rw [bq_integral_exp hs, one_div]
  have hint : Integrable (Function.uncurry f)
      ((volume.restrict (Ioc a b)).prod (volume.restrict (Ioi (0 : ℝ)))) := by
    rw [integrable_prod_iff hmeas]
    refine ⟨(ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun s hs =>
      bq_integrableOn_exp (ha.trans hs.1)), ?_⟩
    have hc : IntegrableOn (fun s : ℝ => s⁻¹) (Ioc a b) :=
      ((continuousOn_inv₀.mono fun s hs => ne_of_gt (ha.trans_le hs.1)).integrableOn_compact
        isCompact_Icc).mono_set Ioc_subset_Icc_self
    exact hc.congr_fun (fun s hs => (hinner s (ha.trans hs.1)).symm) measurableSet_Ioc
  refine ⟨IntegrableOn.congr_fun hint.integral_prod_right (fun t ht => (hrep ht).symm)
    measurableSet_Ioi, ?_⟩
  · rw [setIntegral_congr_fun measurableSet_Ioi hrep]
    have hswap := integral_integral_swap hint
    simp only [f] at hswap
    rw [← hswap]
    have e : EqOn (fun s : ℝ => ∫ t in Ioi (0 : ℝ), Real.exp (-(s * t))) (fun s => s⁻¹) (Ioc a b) :=
      fun s hs => by
        have := hinner s (ha.trans hs.1)
        simpa [f, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using this
    rw [setIntegral_congr_fun measurableSet_Ioc e, ← intervalIntegral.integral_of_le hab,
      integral_inv_of_pos ha hb]

theorem bq_exp_succ (t : ℝ) (k : ℕ) :
    Real.exp (-(((k : ℝ) + 1) * t)) = Real.exp (-t) * Real.exp (-t) ^ k := by
  rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; ring

/-- The finite geometric series `e^{−t}(1 − e^{−nt})/(1 − e^{−t}) = Σ_{k<n} e^{−(k+1)t}`. -/
theorem bq_geom {t : ℝ} (ht : 0 < t) (n : ℕ) :
    (1 - Real.exp (-t) ^ n) * Real.exp (-t) / (1 - Real.exp (-t))
      = ∑ k ∈ Finset.range n, Real.exp (-(((k : ℝ) + 1) * t)) := by
  have hd := (PilotDigamma.one_sub_exp_neg_pos ht).ne'
  have hx : Real.exp (-t) ≠ 1 := fun h => hd (by rw [h]; ring)
  have hx1 : Real.exp (-t) - 1 ≠ 0 := sub_ne_zero.2 hx
  simp_rw [bq_exp_succ, ← Finset.mul_sum, geom_sum_eq hx n]
  rw [mul_div_assoc', div_eq_div_iff hd hx1]
  ring

/-- The `n`-th truncation `∫_0^∞ (1 − e^{−nt}) e^{−t} φ₂(t) dt = H_n − log (n + 1)`. -/
theorem bq_integral_trunc (n : ℕ) :
    ∫ t in Ioi (0 : ℝ), (1 - Real.exp (-t) ^ n) * (Real.exp (-t) * phi2 t)
      = Real.eulerMascheroniSeq n := by
  have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  obtain ⟨hHi, hHv⟩ := bq_frullani one_pos hn
  have hGi : ∀ k ∈ Finset.range n,
      Integrable (fun t => Real.exp (-(((k : ℝ) + 1) * t))) (volume.restrict (Ioi (0 : ℝ))) :=
    fun k _ => bq_integrableOn_exp (by positivity)
  have key : EqOn (fun t => (1 - Real.exp (-t) ^ n) * (Real.exp (-t) * phi2 t))
      (fun t => ∑ k ∈ Finset.range n, Real.exp (-(((k : ℝ) + 1) * t))
        - (Real.exp (-(1 * t)) - Real.exp (-(((n : ℝ) + 1) * t))) / t) (Ioi 0) := by
    intro t ht
    have ht' : (0 : ℝ) < t := ht
    have hd := (PilotDigamma.one_sub_exp_neg_pos ht').ne'
    have htne := ht'.ne'
    simp only
    rw [← bq_geom ht' n, bq_exp_succ, one_mul, phi2]
    field_simp
  rw [setIntegral_congr_fun measurableSet_Ioi key, integral_sub (integrable_finsetSum _ hGi) hHi,
    integral_finsetSum _ hGi, hHv,
    Finset.sum_congr rfl (fun (k : ℕ) _ => bq_integral_exp (c := (k : ℝ) + 1) (by positivity)), div_one,
    Real.eulerMascheroniSeq, harmonic]
  push_cast
  simp only [one_div]

/-- **The Euler–Mascheroni integral**: `∫_0^∞ e^{−t}(1/(1 − e^{−t}) − 1/t) dt = γ`. -/
theorem integral_exp_mul_phi2_eq_eulerMascheroni :
    ∫ t in Ioi (0 : ℝ), Real.exp (-t) * phi2 t = Real.eulerMascheroniConstant := by
  have hF : IntegrableOn (fun t => Real.exp (-t) * phi2 t) (Ioi 0) := by
    simpa using integrableOn_exp_mul_phi2 one_pos
  have hmF : Measurable (fun t => Real.exp (-t) * phi2 t) :=
    (Real.measurable_exp.comp measurable_neg).mul measurable_phi2
  have hx : ∀ t : ℝ, 0 < t → 0 ≤ Real.exp (-t) ∧ Real.exp (-t) < 1 := fun t ht =>
    ⟨(Real.exp_pos _).le, Real.exp_lt_one_iff.2 (by linarith)⟩
  have hFn : ∀ t : ℝ, 0 < t → 0 ≤ Real.exp (-t) * phi2 t := fun t ht =>
    mul_nonneg (Real.exp_pos _).le (phi2_pos ht).le
  have hf : ∀ n : ℕ, Integrable (fun t => (1 - Real.exp (-t) ^ n) * (Real.exp (-t) * phi2 t))
      (volume.restrict (Ioi 0)) := by
    intro n
    refine Integrable.mono hF (((measurable_const.sub
      ((Real.measurable_exp.comp measurable_neg).pow_const n)).mul hmF).aestronglyMeasurable) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_)
    obtain ⟨h0, h1⟩ := hx t ht
    have hp1 : Real.exp (-t) ^ n ≤ 1 := pow_le_one₀ h0 h1.le
    have hp0 : 0 ≤ Real.exp (-t) ^ n := pow_nonneg h0 n
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_nonneg (hFn t ht),
      abs_of_nonneg (sub_nonneg.2 hp1)]
    exact mul_le_of_le_one_left (hFn t ht) (by linarith)
  have hmono : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))),
      Monotone fun n : ℕ => (1 - Real.exp (-t) ^ n) * (Real.exp (-t) * phi2 t) := by
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_)
    intro m n hmn
    obtain ⟨h0, h1⟩ := hx t ht
    have : Real.exp (-t) ^ n ≤ Real.exp (-t) ^ m := pow_le_pow_of_le_one h0 h1.le hmn
    exact mul_le_mul_of_nonneg_right (by linarith) (hFn t ht)
  have htend : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))),
      Tendsto (fun n : ℕ => (1 - Real.exp (-t) ^ n) * (Real.exp (-t) * phi2 t)) atTop
        (𝓝 (Real.exp (-t) * phi2 t)) := by
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_)
    obtain ⟨h0, h1⟩ := hx t ht
    have := ((tendsto_pow_atTop_nhds_zero_of_lt_one h0 h1).const_sub 1).mul_const
      (Real.exp (-t) * phi2 t)
    simpa using this
  have hlim := integral_tendsto_of_tendsto_of_monotone hf hF hmono htend
  have e : (fun n : ℕ => ∫ t in Ioi (0 : ℝ), (1 - Real.exp (-t) ^ n) * (Real.exp (-t) * phi2 t))
      = Real.eulerMascheroniSeq := funext bq_integral_trunc
  rw [e] at hlim
  exact tendsto_nhds_unique hlim Real.tendsto_eulerMascheroniSeq

/-- **Binet at `3/4`**: `∫_0^∞ e^{−3t/4} φ₂(t) dt = log (3/4) − ψ(3/4)`. -/
theorem integral_hK_eq :
    ∫ t in Ioi (0 : ℝ), Real.exp (-(3 / 4 * t)) * phi2 t
      = Real.log (3 / 4) - (Complex.digamma (3 / 4 : ℂ)).re := by
  have hz : 0 < (3 / 4 : ℂ).re := by norm_num
  have hw : 0 < (1 : ℂ).re := by norm_num
  obtain ⟨-, hG⟩ := PilotDigamma.digamma_sub_eq_integral hz hw
  have hgk : ∀ t : ℝ, PilotDigamma.gaussK (3 / 4) 1 t
      = (((Real.exp (-t) - Real.exp (-(3 / 4 * t))) / (1 - Real.exp (-t)) : ℝ) : ℂ) := by
    intro t
    simp only [PilotDigamma.gaussK, one_mul]
    push_cast
    ring
  have hre : (Complex.digamma (3 / 4 : ℂ)).re + Real.eulerMascheroniConstant
      = ∫ t in Ioi (0 : ℝ), (Real.exp (-t) - Real.exp (-(3 / 4 * t))) / (1 - Real.exp (-t)) := by
    simp only [hgk] at hG
    rw [integral_complex_ofReal, Complex.digamma_one] at hG
    have := congrArg Complex.re hG
    simp only [Complex.sub_re, Complex.neg_re, Complex.ofReal_re] at this
    linarith
  have hA := integrableOn_exp_mul_phi2 (c := 1) one_pos
  have hB := integrableOn_exp_mul_phi2 (c := 3 / 4) (by norm_num)
  obtain ⟨hCi, hCv⟩ := bq_frullani (a := 3 / 4) (b := 1) (by norm_num) (by norm_num)
  have hsplit : EqOn (fun t => (Real.exp (-t) - Real.exp (-(3 / 4 * t))) / (1 - Real.exp (-t)))
      (fun t => (Real.exp (-(1 * t)) * phi2 t - Real.exp (-(3 / 4 * t)) * phi2 t)
        - (Real.exp (-(3 / 4 * t)) - Real.exp (-(1 * t))) / t) (Ioi 0) := by
    intro t ht
    have ht' : (0 : ℝ) < t := ht
    have hd := (PilotDigamma.one_sub_exp_neg_pos ht').ne'
    have htne := ht'.ne'
    simp only [one_mul, phi2]
    field_simp
    ring
  have hAB : IntegrableOn (fun t => Real.exp (-(1 * t)) * phi2 t - Real.exp (-(3 / 4 * t)) * phi2 t)
      (Ioi 0) := hA.sub hB
  rw [setIntegral_congr_fun measurableSet_Ioi hsplit, integral_sub hAB hCi,
    integral_sub hA hB, hCv] at hre
  have hA' : ∫ t in Ioi (0 : ℝ), Real.exp (-(1 * t)) * phi2 t = Real.eulerMascheroniConstant := by
    simpa using integral_exp_mul_phi2_eq_eulerMascheroni
  have hlog : Real.log (1 / (3 / 4)) = -Real.log (3 / 4) := by rw [one_div, Real.log_inv]
  rw [hA', hlog] at hre
  linarith

/-! ## The archimedean kernel `K(u) = e^{−u/2}/sinh u` -/

theorem archKer_three_quarters (u : ℝ) :
    archKer (3 / 4) u = Real.exp (-(u / 2)) / Real.sinh u := by
  unfold archKer
  rw [show (1 - 2 * (3 / 4 : ℝ)) * u = -(u / 2) by ring]

theorem measurable_K : Measurable (archKer (3 / 4)) := by
  unfold archKer; fun_prop

theorem K_pos {u : ℝ} (hu : 0 < u) : 0 < archKer (3 / 4) u := by
  rw [archKer_three_quarters]
  exact div_pos (Real.exp_pos _) (Real.sinh_pos_iff.2 hu)

theorem K_le_inv {u : ℝ} (hu : 0 < u) : archKer (3 / 4) u ≤ 1 / u := by
  rw [archKer_three_quarters, div_le_div_iff₀ (Real.sinh_pos_iff.2 hu) hu]
  have h1 : Real.exp (-(u / 2)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have h2 : u ≤ Real.sinh u := Real.self_le_sinh_iff.2 hu.le
  nlinarith

theorem K_eq_exp {u : ℝ} (hu : 0 < u) :
    archKer (3 / 4) u = 2 * Real.exp (-(3 / 2 * u)) / (1 - Real.exp (-(2 * u))) := by
  have hs : 0 < Real.sinh u := Real.sinh_pos_iff.2 hu
  have hd : 0 < 1 - Real.exp (-(2 * u)) := by
    have : Real.exp (-(2 * u)) < 1 := by
      rw [← Real.exp_zero]; exact Real.exp_lt_exp.2 (by linarith)
    linarith
  rw [archKer_three_quarters, div_eq_div_iff hs.ne' hd.ne', Real.sinh_eq]
  have e1 : Real.exp (-(3 / 2 * u)) = Real.exp (-(u / 2)) * Real.exp (-u) := by
    rw [← Real.exp_add]; congr 1; ring
  have e2 : Real.exp (-(2 * u)) = Real.exp (-u) * Real.exp (-u) := by
    rw [← Real.exp_add]; congr 1; ring
  have e3 : Real.exp u * Real.exp (-u) = 1 := by rw [← Real.exp_add]; simp
  rw [e1, e2]
  linear_combination (-(Real.exp (-(u / 2)))) * e3

theorem K_le_exp {u : ℝ} (hu : 0 < u) :
    archKer (3 / 4) u ≤ 2 * Real.exp (-(3 / 2 * u)) / (1 - Real.exp (-(2 * u))) :=
  (K_eq_exp hu).le

/-- On `u ≥ 2a`: `K u ≤ (2/(1 − e^{−4a})) e^{−3u/2}`. -/
theorem K_le_exp_tail {a u : ℝ} (ha : 0 < a) (hu : 2 * a ≤ u) :
    archKer (3 / 4) u ≤ 2 / (1 - Real.exp (-(4 * a))) * Real.exp (-(3 / 2) * u) := by
  have hu0 : 0 < u := by linarith
  have hd : 0 < 1 - Real.exp (-(4 * a)) := by
    have : Real.exp (-(4 * a)) < 1 := by
      rw [← Real.exp_zero]; exact Real.exp_lt_exp.2 (by linarith)
    linarith
  have hle : Real.exp (-(2 * u)) ≤ Real.exp (-(4 * a)) := Real.exp_le_exp.2 (by linarith)
  have e : 2 / (1 - Real.exp (-(4 * a))) * Real.exp (-(3 / 2) * u) =
      2 * Real.exp (-(3 / 2 * u)) / (1 - Real.exp (-(4 * a))) := by
    rw [show -(3 / 2) * u = -(3 / 2 * u) by ring]; ring
  rw [K_eq_exp hu0, e]
  refine div_le_div_of_nonneg_left ?_ hd ?_
  · have := Real.exp_pos (-(3 / 2 * u)); linarith
  · linarith

theorem integrableOn_K_Ioi {a : ℝ} (ha : 0 < a) : IntegrableOn (archKer (3 / 4)) (Ioi (2 * a)) := by
  have hg : IntegrableOn (fun x => 2 / (1 - Real.exp (-(4 * a))) * Real.exp (-(3 / 2) * x))
      (Ioi (2 * a)) :=
    Integrable.const_mul (exp_neg_integrableOn_Ioi (2 * a) (by norm_num : (0 : ℝ) < 3 / 2)) _
  refine Integrable.mono' hg measurable_K.aestronglyMeasurable ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioi (fun u hu => ?_)
  have hu' : 2 * a < u := hu
  rw [Real.norm_eq_abs, abs_of_pos (K_pos (by linarith))]
  exact K_le_exp_tail ha hu'.le

/-- The tail `∫_{2a}^∞ K ≤ (4/3) e^{−3a}/(1 − e^{−4a})`. -/
theorem integral_K_tail_le {a : ℝ} (ha : 0 < a) :
    ∫ u in Ioi (2 * a), archKer (3 / 4) u ≤
      4 / 3 * Real.exp (-(3 * a)) / (1 - Real.exp (-(4 * a))) := by
  have hd : 0 < 1 - Real.exp (-(4 * a)) := by
    have : Real.exp (-(4 * a)) < 1 := by
      rw [← Real.exp_zero]; exact Real.exp_lt_exp.2 (by linarith)
    linarith
  have hg : IntegrableOn (fun x => 2 / (1 - Real.exp (-(4 * a))) * Real.exp (-(3 / 2) * x))
      (Ioi (2 * a)) :=
    Integrable.const_mul (exp_neg_integrableOn_Ioi (2 * a) (by norm_num : (0 : ℝ) < 3 / 2)) _
  calc ∫ u in Ioi (2 * a), archKer (3 / 4) u
      ≤ ∫ u in Ioi (2 * a), 2 / (1 - Real.exp (-(4 * a))) * Real.exp (-(3 / 2) * u) :=
        setIntegral_mono_on (integrableOn_K_Ioi ha) hg measurableSet_Ioi
          (fun u hu => K_le_exp_tail ha (le_of_lt hu))
    _ = 2 / (1 - Real.exp (-(4 * a))) * (-Real.exp (-(3 / 2) * (2 * a)) / (-(3 / 2))) := by
        rw [integral_const_mul, integral_exp_mul_Ioi (by norm_num)]
    _ = 4 / 3 * Real.exp (-(3 * a)) / (1 - Real.exp (-(4 * a))) := by
        rw [show -(3 / 2) * (2 * a) = -(3 * a) by ring]
        field_simp
        ring

/-! ## `φ(u) = u K(u)/2` -/

/-- `φ(u) = u K(u)/2`. -/
def phiK (u : ℝ) : ℝ := u * archKer (3 / 4) u / 2

/-- `φ'(u) = e^{−u/2}((1 − u/2) sinh u − u cosh u)/(2 sinh² u)`. -/
def phiD (u : ℝ) : ℝ :=
  Real.exp (-(u / 2)) * ((1 - u / 2) * Real.sinh u - u * Real.cosh u) / (2 * Real.sinh u ^ 2)

theorem phiK_pos {u : ℝ} (hu : 0 < u) : 0 < phiK u :=
  div_pos (mul_pos hu (K_pos hu)) two_pos

/-- `sinh u ≤ u cosh u` for `u ≥ 0` (i.e. `tanh u ≤ u`). -/
theorem sinh_le_mul_cosh {u : ℝ} (hu : 0 ≤ u) : Real.sinh u ≤ u * Real.cosh u := by
  have hmono : MonotoneOn (fun v => v * Real.cosh v - Real.sinh v) (Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0) ?_ ?_ ?_
    · exact (by fun_prop : Continuous (fun v => v * Real.cosh v - Real.sinh v)).continuousOn
    · exact (by fun_prop : Differentiable ℝ (fun v => v * Real.cosh v - Real.sinh v)).differentiableOn
    · intro x hx
      rw [interior_Ici] at hx
      have hx' : 0 < x := hx
      have hd : HasDerivAt (fun v => v * Real.cosh v - Real.sinh v) (x * Real.sinh x) x := by
        have := ((hasDerivAt_id' x).mul (Real.hasDerivAt_cosh x)).sub (Real.hasDerivAt_sinh x)
        convert this using 1; ring
      rw [hd.deriv]
      exact mul_nonneg hx'.le (Real.sinh_nonneg_iff.2 hx'.le)
  have h := hmono self_mem_Ici hu hu
  have h0 : (0 : ℝ) * Real.cosh 0 - Real.sinh 0 = 0 := by simp
  simp only at h
  linarith

theorem hasDerivAt_phiK {u : ℝ} (hu : 0 < u) : HasDerivAt phiK (phiD u) u := by
  have hs : Real.sinh u ≠ 0 := (Real.sinh_pos_iff.2 hu).ne'
  have hf : phiK = fun v => v * (Real.exp (-(v / 2)) / Real.sinh v) / 2 := by
    funext v; rw [phiK, archKer_three_quarters]
  rw [hf]
  have he : HasDerivAt (fun v => Real.exp (-(v / 2))) (Real.exp (-(u / 2)) * (-(1 / 2))) u :=
    ((hasDerivAt_id' u).div_const 2).neg.exp
  have hk : HasDerivAt (fun v => Real.exp (-(v / 2)) / Real.sinh v)
      ((Real.exp (-(u / 2)) * (-(1 / 2)) * Real.sinh u - Real.exp (-(u / 2)) * Real.cosh u) /
        Real.sinh u ^ 2) u := he.div (Real.hasDerivAt_sinh u) hs
  have hm : HasDerivAt (fun v => v * (Real.exp (-(v / 2)) / Real.sinh v) / 2)
      ((1 * (Real.exp (-(u / 2)) / Real.sinh u) + u * ((Real.exp (-(u / 2)) * (-(1 / 2)) *
        Real.sinh u - Real.exp (-(u / 2)) * Real.cosh u) / Real.sinh u ^ 2)) / 2) u :=
    ((hasDerivAt_id' u).mul hk).div_const 2
  convert hm using 1
  unfold phiD
  field_simp
  ring

theorem phiD_nonpos {u : ℝ} (hu : 0 < u) : phiD u ≤ 0 := by
  unfold phiD
  have hs : 0 < Real.sinh u := Real.sinh_pos_iff.2 hu
  have hc := sinh_le_mul_cosh hu.le
  have hE := Real.exp_pos (-(u / 2))
  have hnum : (1 - u / 2) * Real.sinh u - u * Real.cosh u ≤ 0 := by nlinarith
  refine div_nonpos_of_nonpos_of_nonneg ?_ (by positivity)
  nlinarith

/-- `φ(u) = u K(u)/2` is at most `1/2`. -/
theorem uK_div_two_le {u : ℝ} (hu : 0 < u) : u * archKer (3 / 4) u / 2 ≤ 1 / 2 := by
  have h := K_le_inv hu
  rw [le_div_iff₀ hu] at h
  nlinarith

/-- `φ(u) = u K(u)/2` is non-increasing on `(0, ∞)`. -/
theorem uK_div_two_antitoneOn : AntitoneOn (fun u => u * archKer (3 / 4) u / 2) (Ioi 0) := by
  have : AntitoneOn phiK (Ioi 0) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ioi 0) ?_ ?_ ?_
    · intro x hx; exact (hasDerivAt_phiK hx).continuousAt.continuousWithinAt
    · rw [interior_Ioi]; intro x hx
      exact (hasDerivAt_phiK hx).differentiableAt.differentiableWithinAt
    · rw [interior_Ioi]; intro x hx
      rw [(hasDerivAt_phiK hx).deriv]; exact phiD_nonpos hx
  exact this

/-! ## Integrability -/

theorem intervalIntegrable_of_bdd {f : ℝ → ℝ} (hf : Measurable f) {M b c : ℝ} (hb : 0 ≤ b)
    (hbc : b ≤ c) (hM : ∀ u, 0 < u → |f u| ≤ M) : IntervalIntegrable f volume b c := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hbc]
  refine Measure.integrableOn_of_bounded (M := M) measure_Ioc_lt_top.ne hf.aestronglyMeasurable ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioc (fun u hu => ?_)
  rw [Real.norm_eq_abs]; exact hM u (lt_of_le_of_lt hb hu.1)

theorem abs_uK_cos_le {ω u : ℝ} (hu : 0 < u) :
    |u / 2 * archKer (3 / 4) u * Real.cos (ω * u)| ≤ 1 / 2 := by
  have h1 : 0 ≤ u / 2 * archKer (3 / 4) u := mul_nonneg (by linarith) (K_pos hu).le
  have h2 : u / 2 * archKer (3 / 4) u ≤ 1 / 2 := by
    have := uK_div_two_le hu; linarith
  rw [abs_mul, abs_of_nonneg h1]
  calc u / 2 * archKer (3 / 4) u * |Real.cos (ω * u)| ≤ 1 / 2 * 1 :=
        mul_le_mul h2 (Real.abs_cos_le_one _) (abs_nonneg _) (by norm_num)
    _ = 1 / 2 := by norm_num

theorem abs_K_sin_le_omega {ω u : ℝ} (hω : 0 < ω) (hu : 0 < u) :
    |archKer (3 / 4) u * Real.sin (ω * u)| ≤ ω := by
  have hK := K_pos hu
  have hKi := K_le_inv hu
  have hu0 : u ≠ 0 := hu.ne'
  rw [abs_mul, abs_of_pos hK]
  have hs : |Real.sin (ω * u)| ≤ ω * u := by
    have := Real.abs_sin_le_abs (x := ω * u); rwa [abs_of_pos (mul_pos hω hu)] at this
  calc archKer (3 / 4) u * |Real.sin (ω * u)| ≤ (1 / u) * (ω * u) :=
        mul_le_mul hKi hs (abs_nonneg _) (by positivity)
    _ = ω := by field_simp

theorem abs_K_sin_le_inv {ω u : ℝ} (hu : 0 < u) :
    |archKer (3 / 4) u * Real.sin (ω * u)| ≤ 1 / u := by
  have hK := K_pos hu
  rw [abs_mul, abs_of_pos hK]
  calc archKer (3 / 4) u * |Real.sin (ω * u)| ≤ archKer (3 / 4) u * 1 :=
        mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) hK.le
    _ = archKer (3 / 4) u := mul_one _
    _ ≤ 1 / u := K_le_inv hu

theorem integrableOn_uK_cos {a ω : ℝ} (ha : 0 < a) :
    IntegrableOn (fun u => u / 2 * archKer (3 / 4) u * Real.cos (ω * u)) (Ioc 0 (2 * a)) := by
  have h := intervalIntegrable_of_bdd (f := fun u => u / 2 * archKer (3 / 4) u * Real.cos (ω * u))
    (by unfold archKer; fun_prop) le_rfl (by linarith : (0 : ℝ) ≤ 2 * a)
    (fun u hu => abs_uK_cos_le hu)
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).1 h

theorem integrableOn_K_sin {a ω : ℝ} (ha : 0 < a) (hω : 0 < ω) :
    IntegrableOn (fun u => archKer (3 / 4) u * Real.sin (ω * u)) (Ioc 0 (2 * a)) := by
  have h := intervalIntegrable_of_bdd (f := fun u => archKer (3 / 4) u * Real.sin (ω * u))
    (by unfold archKer; fun_prop) le_rfl (by linarith : (0 : ℝ) ≤ 2 * a)
    (fun u hu => abs_K_sin_le_omega hω hu)
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).1 h

/-! ## The oscillatory bounds -/

/-- `|∫_0^{2a} (u/2) K(u) cos(ωu) du| ≤ 1/(2ω)`. -/
theorem abs_integral_uK_cos_le {a ω : ℝ} (ha : 0 < a) (hω : 0 < ω) :
    |∫ u in Ioc (0 : ℝ) (2 * a), u / 2 * archKer (3 / 4) u * Real.cos (ω * u)| ≤ 1 / (2 * ω) := by
  have hfeq : (fun u => u / 2 * archKer (3 / 4) u * Real.cos (ω * u)) =
      fun u => phiK u * Real.cos (ω * u) := by
    funext u; unfold phiK; ring
  rw [← intervalIntegral.integral_of_le (by linarith : (0 : ℝ) ≤ 2 * a), hfeq]
  have hbd : ∀ u, 0 < u → |phiK u * Real.cos (ω * u)| ≤ 1 / 2 := by
    intro u hu
    have := abs_uK_cos_le (ω := ω) hu
    rwa [show u / 2 * archKer (3 / 4) u = phiK u by unfold phiK; ring] at this
  have hmeas : Measurable (fun u => phiK u * Real.cos (ω * u)) := by
    unfold phiK archKer; fun_prop
  have hII : ∀ b c, 0 ≤ b → b ≤ c →
      IntervalIntegrable (fun u => phiK u * Real.cos (ω * u)) volume b c :=
    fun b c hb hbc => intervalIntegrable_of_bdd hmeas hb hbc hbd
  refine le_of_forall_pos_le_add (fun ε hε => ?_)
  obtain ⟨δ, hδpos, hδε, hδa⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ ε ∧ δ ≤ a :=
    ⟨min ε a, lt_min hε ha, min_le_left _ _, min_le_right _ _⟩
  have hδ2a : δ ≤ 2 * a := by linarith
  rw [← intervalIntegral.integral_add_adjacent_intervals (hII 0 δ le_rfl hδpos.le)
    (hII δ (2 * a) hδpos.le hδ2a)]
  -- the piece near `0`
  have h1 : |∫ u in (0 : ℝ)..δ, phiK u * Real.cos (ω * u)| ≤ 1 / 2 * δ := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := δ) (C := 1 / 2)
      (f := fun u => phiK u * Real.cos (ω * u)) (fun x hx => by
        rw [uIoc_of_le hδpos.le] at hx
        rw [Real.norm_eq_abs]; exact hbd x hx.1)
    rw [Real.norm_eq_abs, sub_zero, abs_of_pos hδpos] at this
    exact this
  -- integration by parts on `[δ, 2a]`
  have hφd : ∀ x ∈ uIcc δ (2 * a), HasDerivAt phiK (phiD x) x := by
    intro x hx; rw [uIcc_of_le hδ2a] at hx; exact hasDerivAt_phiK (by linarith [hx.1])
  have hvd : ∀ x ∈ uIcc δ (2 * a),
      HasDerivAt (fun u => Real.sin (ω * u) / ω) (Real.cos (ω * x)) x := by
    intro x _
    have := (((hasDerivAt_id' x).const_mul ω).sin).div_const ω
    convert this using 1
    rw [mul_one, mul_div_assoc, div_self hω.ne', mul_one]
  have hDcont : ContinuousOn phiD (uIcc δ (2 * a)) := by
    rw [uIcc_of_le hδ2a]
    unfold phiD
    refine ContinuousOn.div (by fun_prop) (by fun_prop) (fun x hx => ?_)
    have : 0 < Real.sinh x := Real.sinh_pos_iff.2 (by linarith [hx.1])
    exact mul_ne_zero two_ne_zero (pow_ne_zero 2 this.ne')
  have hDint : IntervalIntegrable phiD volume δ (2 * a) := hDcont.intervalIntegrable
  have hcint : IntervalIntegrable (fun x => Real.cos (ω * x)) volume δ (2 * a) :=
    (by fun_prop : Continuous fun x => Real.cos (ω * x)).intervalIntegrable _ _
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hφd hvd hDint hcint
  have hpt : ∀ x, 0 < x → ‖phiD x * (Real.sin (ω * x) / ω)‖ ≤ -phiD x * (1 / ω) := by
    intro x hx
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonpos (phiD_nonpos hx)]
    refine mul_le_mul_of_nonneg_left ?_ (by linarith [phiD_nonpos hx])
    rw [abs_div, abs_of_pos hω]
    exact div_le_div_of_nonneg_right (Real.abs_sin_le_one _) hω.le
  have hJ : |∫ x in δ..(2 * a), phiD x * (Real.sin (ω * x) / ω)| ≤
      (phiK δ - phiK (2 * a)) * (1 / ω) := by
    have hle : ‖∫ x in δ..(2 * a), phiD x * (Real.sin (ω * x) / ω)‖ ≤
        ∫ x in δ..(2 * a), -phiD x * (1 / ω) :=
      intervalIntegral.norm_integral_le_of_norm_le hδ2a
        (Eventually.of_forall (fun x hx => hpt x (by linarith [hx.1]))) (hDint.neg.mul_const _)
    rw [Real.norm_eq_abs] at hle
    refine hle.trans (le_of_eq ?_)
    rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_neg,
      intervalIntegral.integral_eq_sub_of_hasDerivAt hφd hDint]
    ring
  have hφ2a : 0 ≤ phiK (2 * a) := (phiK_pos (by linarith)).le
  have hφδ0 : 0 ≤ phiK δ := (phiK_pos hδpos).le
  have hφδ : phiK δ ≤ 1 / 2 := uK_div_two_le hδpos
  have hA : |phiK (2 * a) * (Real.sin (ω * (2 * a)) / ω)| ≤ phiK (2 * a) * (1 / ω) := by
    rw [abs_mul, abs_of_nonneg hφ2a]
    refine mul_le_mul_of_nonneg_left ?_ hφ2a
    rw [abs_div, abs_of_pos hω]
    exact div_le_div_of_nonneg_right (Real.abs_sin_le_one _) hω.le
  have hB : |phiK δ * (Real.sin (ω * δ) / ω)| ≤ 1 / 2 * δ := by
    rw [abs_mul, abs_of_nonneg hφδ0]
    refine mul_le_mul hφδ ?_ (abs_nonneg _) (by norm_num)
    rw [abs_div, abs_of_pos hω, div_le_iff₀ hω]
    calc |Real.sin (ω * δ)| ≤ |ω * δ| := Real.abs_sin_le_abs
      _ = δ * ω := by rw [abs_of_pos (mul_pos hω hδpos)]; ring
  rw [hibp]
  have hw : 0 < 1 / ω := by positivity
  have hkey : phiK δ * (1 / ω) ≤ 1 / 2 * (1 / ω) := mul_le_mul_of_nonneg_right hφδ hw.le
  have h2w : 1 / (2 * ω) = 1 / 2 * (1 / ω) := by ring
  have e1 := abs_le.1 h1
  have eA := abs_le.1 hA
  have eB := abs_le.1 hB
  have eJ := abs_le.1 hJ
  rw [abs_le]
  constructor <;> nlinarith

/-- `|∫_0^{2a} K(u) sin(ωu) du| ≤ 1 + log(2aω)` when `2aω ≥ 1`. -/
theorem abs_integral_K_sin_le {a ω : ℝ} (ha : 0 < a) (hω : 0 < ω) (h1 : 1 ≤ 2 * a * ω) :
    |∫ u in Ioc (0 : ℝ) (2 * a), archKer (3 / 4) u * Real.sin (ω * u)| ≤
      1 + Real.log (2 * a * ω) := by
  have hc : 0 < 1 / ω := by positivity
  have hc2 : 1 / ω ≤ 2 * a := by rw [div_le_iff₀ hω]; linarith
  have hmeas : Measurable (fun u => archKer (3 / 4) u * Real.sin (ω * u)) := by
    unfold archKer; fun_prop
  have hII : ∀ b c, 0 ≤ b → b ≤ c →
      IntervalIntegrable (fun u => archKer (3 / 4) u * Real.sin (ω * u)) volume b c :=
    fun b c hb hbc => intervalIntegrable_of_bdd hmeas hb hbc (fun u hu => abs_K_sin_le_omega hω hu)
  rw [← intervalIntegral.integral_of_le (by linarith : (0 : ℝ) ≤ 2 * a),
    ← intervalIntegral.integral_add_adjacent_intervals (hII 0 (1 / ω) le_rfl hc.le)
      (hII (1 / ω) (2 * a) hc.le hc2)]
  have e1 : |∫ u in (0 : ℝ)..(1 / ω), archKer (3 / 4) u * Real.sin (ω * u)| ≤ 1 := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1 / ω) (C := ω)
      (f := fun u => archKer (3 / 4) u * Real.sin (ω * u)) (fun x hx => by
        rw [uIoc_of_le hc.le] at hx
        rw [Real.norm_eq_abs]; exact abs_K_sin_le_omega hω hx.1)
    rw [Real.norm_eq_abs, sub_zero, abs_of_pos hc, mul_one_div_cancel hω.ne'] at this
    exact this
  have e2 : |∫ u in (1 / ω)..(2 * a), archKer (3 / 4) u * Real.sin (ω * u)| ≤
      Real.log (2 * a * ω) := by
    have hg : IntervalIntegrable (fun u : ℝ => 1 / u) volume (1 / ω) (2 * a) := by
      refine ContinuousOn.intervalIntegrable ?_
      rw [uIcc_of_le hc2]
      exact continuousOn_const.div continuousOn_id (fun x hx => (lt_of_lt_of_le hc hx.1).ne')
    have hle : ‖∫ u in (1 / ω)..(2 * a), archKer (3 / 4) u * Real.sin (ω * u)‖ ≤
        ∫ u in (1 / ω)..(2 * a), 1 / u :=
      intervalIntegral.norm_integral_le_of_norm_le hc2
        (Eventually.of_forall (fun x hx => by
          rw [Real.norm_eq_abs]; exact abs_K_sin_le_inv (lt_trans hc hx.1))) hg
    rw [Real.norm_eq_abs, integral_one_div_of_pos hc (by linarith)] at hle
    rwa [show 2 * a / (1 / ω) = 2 * a * ω by field_simp] at hle
  have f1 := abs_le.1 e1
  have f2 := abs_le.1 e2
  rw [abs_le]
  constructor <;> linarith

/-! ## The Gauss integral at shift `¾`, split -/

theorem integrableOn_hK_mul_cos (c : ℝ) : IntegrableOn (fun t : ℝ => hK t * Real.cos (c * t)) (Ioi 0) := by
  refine integrableOn_hK.mono' (measurable_hK.mul (by fun_prop)).aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_)
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hK_nonneg ht)]
  exact mul_le_of_le_one_right (hK_nonneg ht) (Real.abs_cos_le_one _)

/-- **The Gauss integral at shift `¾`, split**:
`Re ψ(¾ + iω/2) − ψ(¾) = ½ log(1 + (ω/2)²/(¾)²) + (log ¾ − ψ(¾)) − ∫₀^∞ h(t) cos(ωt/2) dt`. -/
theorem psiReQ_three_quarters_sub (ω : ℝ) :
    psiReQ (3 / 4) ω - psiReQ (3 / 4) 0
      = Real.log (1 + (ω / 2) ^ 2 / (3 / 4) ^ 2) / 2
        + (Real.log (3 / 4) - (Complex.digamma (3 / 4 : ℂ)).re)
        - ∫ t in Ioi (0 : ℝ), hK t * Real.cos (ω / 2 * t) := by
  obtain ⟨-, hE⟩ := psiReQ_sub (q := 3 / 4) (by norm_num) ω
  rw [hE]
  have h1 := integrableOn_one_sub_cos_mul_exp_div (b := ω / 2) (c := 3 / 4) (by norm_num)
  have h2 := integrableOn_hK
  have h3 := integrableOn_hK_mul_cos (ω / 2)
  have e : EqOn (fun t : ℝ => kkQ (3 / 4) t * (1 - Real.cos (ω * (t / 2))))
      (fun t : ℝ => (1 - Real.cos (ω / 2 * t)) * Real.exp (-(3 / 4 * t)) / t
        + (hK t - hK t * Real.cos (ω / 2 * t))) (Ioi 0) := by
    intro t ht
    simp only
    rw [kkQ_three_quarters_eq ht, show ω * (t / 2) = ω / 2 * t by ring]
    ring
  have h23 : IntegrableOn (fun t : ℝ => hK t - hK t * Real.cos (ω / 2 * t)) (Ioi 0) := h2.sub h3
  rw [setIntegral_congr_fun measurableSet_Ioi e, integral_add h1 h23, integral_sub h2 h3,
    integral_one_sub_cos_mul_exp_div (by norm_num)]
  have hH : ∫ t in Ioi (0 : ℝ), hK t = Real.log (3 / 4) - (Complex.digamma (3 / 4 : ℂ)).re :=
    integral_hK_eq
  rw [hH]
  ring

/-- The oscillatory remainder is at most `3/ω`. -/
theorem abs_integral_hK_cos_half_le {ω : ℝ} (hω : 0 < ω) :
    |∫ t in Ioi (0 : ℝ), hK t * Real.cos (ω / 2 * t)| ≤ 3 / ω := by
  have := abs_integral_hK_cos_le (c := ω / 2) (by positivity)
  calc |∫ t in Ioi (0 : ℝ), hK t * Real.cos (ω / 2 * t)| ≤ 3 / 2 / (ω / 2) := this
    _ = 3 / ω := by field_simp

/-- **`Re ψ(¾ + iω/2) ≤ log √(9/16 + ω²/4) + 3/ω`.** -/
theorem psiReQ_three_quarters_le {ω : ℝ} (hω : 0 < ω) :
    psiReQ (3 / 4) ω ≤ Real.log (Real.sqrt (9 / 16 + ω ^ 2 / 4)) + 3 / ω := by
  have h := psiReQ_three_quarters_sub ω
  have hb := abs_le.1 (abs_integral_hK_cos_half_le hω)
  rw [psiReQ_zero] at h
  have hc : ((3 / 4 : ℝ) : ℂ) = (3 / 4 : ℂ) := by norm_num
  rw [hc] at h
  have e : Real.log (1 + (ω / 2) ^ 2 / (3 / 4) ^ 2) / 2 + Real.log (3 / 4)
      = Real.log (Real.sqrt (9 / 16 + ω ^ 2 / 4)) := by
    have hx : (9 / 16 + ω ^ 2 / 4 : ℝ) = (1 + (ω / 2) ^ 2 / (3 / 4) ^ 2) * (3 / 4) ^ 2 := by ring
    rw [Real.log_sqrt (by positivity), hx, Real.log_mul (by positivity) (by norm_num), Real.log_pow]
    push_cast
    ring
  linarith [h, hb.1, hb.2]

/-! ## The Gauss integral in the `u`-variable -/

/-- **The Gauss integral in the `u`-variable**: `Re ψ(¾ + iω/2) − ψ(¾) = ∫₀^∞ K(u)(1 − cos ωu) du`. -/
theorem psiReQ_three_quarters_sub_u (ω : ℝ) :
    psiReQ (3 / 4) ω - psiReQ (3 / 4) 0
      = ∫ u in Ioi (0 : ℝ), archKer (3 / 4) u * (1 - Real.cos (ω * u)) := by
  obtain ⟨-, hE⟩ := psiReQ_sub (q := 3 / 4) (by norm_num) ω
  rw [hE]
  have h := integral_comp_mul_left_Ioi (fun t : ℝ => kkQ (3 / 4) t * (1 - Real.cos (ω * (t / 2)))) 0
    (by norm_num : (0 : ℝ) < 2)
  simp only [mul_zero, smul_eq_mul] at h
  have h' : ∫ t in Ioi (0 : ℝ), kkQ (3 / 4) t * (1 - Real.cos (ω * (t / 2)))
      = 2 * ∫ x in Ioi (0 : ℝ), kkQ (3 / 4) (2 * x) * (1 - Real.cos (ω * (2 * x / 2))) := by
    rw [h]; ring
  rw [h', ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
  rw [show ω * (2 * u / 2) = ω * u by ring, ← mul_assoc, two_kkQ (3 / 4) hu]

/-- The integrand `K(u)(1 − cos ωu)` is integrable on `(0, ∞)`. -/
theorem integrableOn_K_one_sub_cos (ω : ℝ) :
    IntegrableOn (fun u : ℝ => archKer (3 / 4) u * (1 - Real.cos (ω * u))) (Ioi 0) := by
  obtain ⟨hI, -⟩ := psiReQ_sub (q := 3 / 4) (by norm_num) ω
  have h2 := (integrableOn_Ioi_comp_mul_left_iff (fun t : ℝ => kkQ (3 / 4) t * (1 - Real.cos (ω * (t / 2)))) 0
    (by norm_num : (0 : ℝ) < 2)).2 (by simpa using hI)
  refine IntegrableOn.congr_fun (h2.const_mul 2) (fun u hu => ?_) measurableSet_Ioi
  rw [show ω * (2 * u / 2) = ω * u by ring, ← mul_assoc, two_kkQ (3 / 4) hu]

/-! ## The archimedean term of the packet -/

/-- Splitting a set integral over `(0, ∞)` at `b ≥ 0`. -/
theorem integral_Ioi_split {f : ℝ → ℝ} {b : ℝ} (hb : 0 ≤ b) (hf : IntegrableOn f (Ioi 0)) :
    ∫ u in Ioi (0 : ℝ), f u = (∫ u in Ioc (0 : ℝ) b, f u) + ∫ u in Ioi b, f u := by
  rw [← Set.Ioc_union_Ioi_eq_Ioi hb]
  exact setIntegral_union (Set.disjoint_left.2 fun _ hx hx' => (not_lt.2 hx.2) hx') measurableSet_Ioi
    (hf.mono_set Ioc_subset_Ioi_self) (hf.mono_set (Ioi_subset_Ioi hb))

/-- `‖g‖² = a + sin(2ωa)/(2ω) ≥ 0` once `2aω ≥ 1`. -/
theorem packet_f0_nonneg {a ω : ℝ} (hω : 0 < ω) (h1 : 1 ≤ 2 * a * ω) :
    0 ≤ a + Real.sin (2 * ω * a) / (2 * ω) := by
  have h2ω : 0 < 2 * ω := by positivity
  have hs : -1 / (2 * ω) ≤ Real.sin (2 * ω * a) / (2 * ω) :=
    div_le_div_of_nonneg_right (Real.neg_one_le_sin _) h2ω.le
  have ha : 1 / (2 * ω) ≤ a := by
    rw [div_le_iff₀ h2ω]; linarith
  have e : -1 / (2 * ω) = -(1 / (2 * ω)) := by ring
  linarith

/-- `K(u) cos(ωu)` is integrable on `(2a, ∞)`. -/
theorem integrableOn_K_cos_Ioi {a : ℝ} (ha : 0 < a) (ω : ℝ) :
    IntegrableOn (fun u => archKer (3 / 4) u * Real.cos (ω * u)) (Ioi (2 * a)) := by
  refine (integrableOn_K_Ioi ha).mono' (measurable_K.mul (by fun_prop)).aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun u hu => ?_)
  have hu0 : 0 < u := lt_trans (by linarith) (mem_Ioi.1 hu)
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (K_pos hu0)]
  exact mul_le_of_le_one_right (K_pos hu0).le (Real.abs_cos_le_one _)

/-- **The archimedean term of the packet**: with `f₀ = a + sin(2ωa)/(2ω)`,
`E_{3/4}(g) ≤ f₀·[Re ψ(¾ + iω/2) − ψ(¾)] + f₀·(4/3)e^{−3a}/(1 − e^{−4a}) + 1/(2ω) + (1 + log(2aω))/(2ω)`. -/
theorem packet_archEQ_le {a ω : ℝ} (ha : 0 < a) (hω : 0 < ω) (h1 : 1 ≤ 2 * a * ω) :
    archEQ (3 / 4) (packet a ω)
      ≤ (a + Real.sin (2 * ω * a) / (2 * ω)) * (psiReQ (3 / 4) ω - psiReQ (3 / 4) 0)
        + (a + Real.sin (2 * ω * a) / (2 * ω)) * (4 / 3 * Real.exp (-(3 * a)) / (1 - Real.exp (-(4 * a))))
        + 1 / (2 * ω) + (1 + Real.log (2 * a * ω)) / (2 * ω) := by
  have hf0nn := packet_f0_nonneg hω h1
  obtain ⟨f₀, hf₀⟩ : ∃ f₀ : ℝ, a + Real.sin (2 * ω * a) / (2 * ω) = f₀ := ⟨_, rfl⟩
  obtain ⟨β, hβ⟩ : ∃ β : ℝ, Real.cos (2 * ω * a) / (2 * ω) = β := ⟨_, rfl⟩
  rw [hf₀] at hf0nn ⊢
  have h2a : (0 : ℝ) ≤ 2 * a := by linarith
  have h2ω : 0 < 2 * ω := by positivity
  have hF := archIntegrandQ_integrable (q := 3 / 4) (packet_probe ha hω.le) (by norm_num)
  have hA := integrableOn_K_one_sub_cos ω
  have hB := integrableOn_uK_cos (ω := ω) ha
  have hC := integrableOn_K_sin ha hω
  have hKc := integrableOn_K_cos_Ioi ha ω
  have hf0 : autocorr (packet a ω) 0 = f₀ := by rw [autocorr_zero, packet_normSq ha hω, hf₀]
  -- the piece on `(0, 2a]`
  have eIoc : ∫ u in Ioc (0 : ℝ) (2 * a), archIntegrandQ (3 / 4) (packet a ω) u
      = f₀ * (∫ u in Ioc (0 : ℝ) (2 * a), archKer (3 / 4) u * (1 - Real.cos (ω * u)))
        + ((∫ u in Ioc (0 : ℝ) (2 * a), u / 2 * archKer (3 / 4) u * Real.cos (ω * u))
          + β * ∫ u in Ioc (0 : ℝ) (2 * a), archKer (3 / 4) u * Real.sin (ω * u)) := by
    have e : EqOn (archIntegrandQ (3 / 4) (packet a ω))
        (fun u => f₀ * (archKer (3 / 4) u * (1 - Real.cos (ω * u)))
          + (u / 2 * archKer (3 / 4) u * Real.cos (ω * u)
            + β * (archKer (3 / 4) u * Real.sin (ω * u)))) (Ioc 0 (2 * a)) := by
      intro u hu
      simp only [archIntegrandQ]
      rw [hf0, packet_autocorr ha hω hu.1.le hu.2,
        show ω * (2 * a - u) = 2 * ω * a - ω * u by ring, Real.sin_sub, ← hf₀, ← hβ]
      ring
    have hBC : IntegrableOn (fun u => u / 2 * archKer (3 / 4) u * Real.cos (ω * u)
        + β * (archKer (3 / 4) u * Real.sin (ω * u))) (Ioc 0 (2 * a)) := hB.add (hC.const_mul β)
    rw [setIntegral_congr_fun measurableSet_Ioc e,
      integral_add ((hA.mono_set Ioc_subset_Ioi_self).const_mul f₀) hBC,
      integral_add hB (hC.const_mul β), integral_const_mul, integral_const_mul]
  -- the piece on `(2a, ∞)`
  have eIoi : ∫ u in Ioi (2 * a), archIntegrandQ (3 / 4) (packet a ω) u
      = f₀ * (∫ u in Ioi (2 * a), archKer (3 / 4) u * (1 - Real.cos (ω * u)))
        + f₀ * ∫ u in Ioi (2 * a), archKer (3 / 4) u * Real.cos (ω * u) := by
    have e : EqOn (archIntegrandQ (3 / 4) (packet a ω))
        (fun u => f₀ * (archKer (3 / 4) u * (1 - Real.cos (ω * u)))
          + f₀ * (archKer (3 / 4) u * Real.cos (ω * u))) (Ioi (2 * a)) := by
      intro u hu
      simp only [archIntegrandQ]
      rw [hf0, packet_autocorr_of_le ha (le_of_lt (mem_Ioi.1 hu))]
      ring
    rw [setIntegral_congr_fun measurableSet_Ioi e,
      integral_add ((hA.mono_set (Ioi_subset_Ioi h2a)).const_mul f₀) (hKc.const_mul f₀),
      integral_const_mul, integral_const_mul]
  -- recombination
  have hD := psiReQ_three_quarters_sub_u ω
  rw [integral_Ioi_split h2a hA] at hD
  have hsplit : archEQ (3 / 4) (packet a ω)
      = (∫ u in Ioc (0 : ℝ) (2 * a), archIntegrandQ (3 / 4) (packet a ω) u)
        + ∫ u in Ioi (2 * a), archIntegrandQ (3 / 4) (packet a ω) u := by
    unfold archEQ
    exact integral_Ioi_split h2a hF
  -- the three remainders
  have hB' : (∫ u in Ioc (0 : ℝ) (2 * a), u / 2 * archKer (3 / 4) u * Real.cos (ω * u))
      ≤ 1 / (2 * ω) := (le_abs_self _).trans (abs_integral_uK_cos_le ha hω)
  have hβabs : |β| ≤ 1 / (2 * ω) := by
    rw [← hβ, abs_div, abs_of_pos h2ω]
    exact div_le_div_of_nonneg_right (Real.abs_cos_le_one _) h2ω.le
  have hlog : 0 ≤ 1 + Real.log (2 * a * ω) := by
    have := Real.log_nonneg h1; linarith
  have hC' : β * (∫ u in Ioc (0 : ℝ) (2 * a), archKer (3 / 4) u * Real.sin (ω * u))
      ≤ (1 + Real.log (2 * a * ω)) / (2 * ω) :=
    calc β * (∫ u in Ioc (0 : ℝ) (2 * a), archKer (3 / 4) u * Real.sin (ω * u))
        ≤ |β * (∫ u in Ioc (0 : ℝ) (2 * a), archKer (3 / 4) u * Real.sin (ω * u))| := le_abs_self _
      _ = |β| * |∫ u in Ioc (0 : ℝ) (2 * a), archKer (3 / 4) u * Real.sin (ω * u)| := abs_mul _ _
      _ ≤ 1 / (2 * ω) * (1 + Real.log (2 * a * ω)) :=
          mul_le_mul hβabs (abs_integral_K_sin_le ha hω h1) (abs_nonneg _) (by positivity)
      _ = (1 + Real.log (2 * a * ω)) / (2 * ω) := by ring
  have hKc' : (∫ u in Ioi (2 * a), archKer (3 / 4) u * Real.cos (ω * u))
      ≤ 4 / 3 * Real.exp (-(3 * a)) / (1 - Real.exp (-(4 * a))) := by
    refine le_trans (setIntegral_mono_on hKc (integrableOn_K_Ioi ha) measurableSet_Ioi
      (fun u hu => ?_)) (integral_K_tail_le ha)
    have hu0 : 0 < u := lt_trans (by linarith) (mem_Ioi.1 hu)
    exact mul_le_of_le_one_right (K_pos hu0).le (Real.cos_le_one _)
  have hKc'' := mul_le_mul_of_nonneg_left hKc' hf0nn
  rw [hsplit, eIoc, eIoi, hD]
  nlinarith [hB', hC', hKc'']

/-- **The archimedean total of the packet**: `ψ(¾)‖g‖² + E_{3/4}(g)` against the explicit majorant. -/
theorem packet_arch_total_le {a ω : ℝ} (ha : 0 < a) (hω : 0 < ω) (h1 : 1 ≤ 2 * a * ω) :
    (Complex.digamma (3 / 4 : ℂ)).re * (a + Real.sin (2 * ω * a) / (2 * ω)) + archEQ (3 / 4) (packet a ω)
      ≤ (a + Real.sin (2 * ω * a) / (2 * ω)) * (Real.log (Real.sqrt (9 / 16 + ω ^ 2 / 4)) + 3 / ω)
        + (a + Real.sin (2 * ω * a) / (2 * ω)) * (4 / 3 * Real.exp (-(3 * a)) / (1 - Real.exp (-(4 * a))))
        + 1 / (2 * ω) + (1 + Real.log (2 * a * ω)) / (2 * ω) := by
  have hE := packet_archEQ_le ha hω h1
  have hf0nn := packet_f0_nonneg hω h1
  have hψ := mul_le_mul_of_nonneg_left (psiReQ_three_quarters_le hω) hf0nn
  rw [psiReQ_zero, show ((3 / 4 : ℝ) : ℂ) = (3 / 4 : ℂ) by norm_num] at hE
  nlinarith [hE, hψ]

end PsiOmega

#print axioms PsiOmega.integral_one_sub_cos_mul_exp_div
#print axioms PsiOmega.integral_exp_sub_exp_div
#print axioms PsiOmega.kkQ_three_quarters_eq
#print axioms PsiOmega.one_half_le_phi2
#print axioms PsiOmega.deriv_phi2_nonneg
#print axioms PsiOmega.abs_integral_hK_cos_le
#print axioms PsiOmega.integral_exp_mul_phi2_eq_eulerMascheroni
#print axioms PsiOmega.integral_hK_eq
#print axioms PsiOmega.K_le_inv
#print axioms PsiOmega.integral_K_tail_le
#print axioms PsiOmega.uK_div_two_antitoneOn
#print axioms PsiOmega.abs_integral_uK_cos_le
#print axioms PsiOmega.abs_integral_K_sin_le
#print axioms PsiOmega.psiReQ_three_quarters_sub
#print axioms PsiOmega.psiReQ_three_quarters_le
#print axioms PsiOmega.psiReQ_three_quarters_sub_u
#print axioms PsiOmega.packet_archEQ_le
#print axioms PsiOmega.packet_arch_total_le
