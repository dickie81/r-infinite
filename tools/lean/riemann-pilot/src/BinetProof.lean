import Mathlib
import DigammaGauss

/-! # Binet's second formula, proved (round 155): discharging `BinetFormula`

`ψ(z) = log z − 1/(2z) − 2∫_0^∞ t dt/((t² + z²)(e^{2πt} − 1))` for `Re z > 0`.

* **C. ψ as a Laplace transform.** `ψ(z) = log z − 1/(2z) − ∫_0^∞ e^{−zs}φ(s) ds`, with
  `φ(s) = 1/(1 − e^{−s}) − 1/s − 1/2` (`|φ| ≤ ½`). Gauss's formula (round 154), the complex Frullani
  integral `log z − log w = ∫_0^∞ (e^{−ws} − e^{−zs})/s ds` (Fubini over the segment `[w, z]`) and
  `1/z = ∫e^{−zs}` show that `ψ(z) − log z + 1/(2z) + ∫e^{−zs}φ` does not depend on `z`. At `z = n + 1`
  it tends to `0` (`H_n − log(n + 1) → γ`).
* **D. φ as a sine transform.** `φ(s) = 2∫_0^∞ sin(st)/(e^{2πt} − 1) dt`: expand
  `1/(e^{2πt} − 1) = Σ_{n≥1} e^{−2πnt}`, integrate termwise to `Σ 2s/(s² + 4π²n²)`, and sum by the
  Mittag-Leffler expansion of `cot` (Mathlib's `cot_series_rep'`) at `x = is/2π`.
* **E. Fubini.** `∫_0^∞ e^{−zs} sin(st) ds = t/(z² + t²)`.
-/

open Filter Topology MeasureTheory Set
open scoped Real

noncomputable section

namespace PilotDigamma

/-! ## C1. The kernel `φ` -/

/-- `φ(s) = 1/(1 − e^{−s}) − 1/s − 1/2`. -/
def phiB (s : ℝ) : ℝ := 1 / (1 - Real.exp (-s)) - 1 / s - 1 / 2

theorem abs_phiB_le {s : ℝ} (hs : 0 < s) : |phiB s| ≤ 1 / 2 := by
  have hd := one_sub_exp_neg_pos hs
  have h2 : (1 + s) * Real.exp (-s) ≤ 1 := by
    have e : Real.exp s * Real.exp (-s) = 1 := by rw [← Real.exp_add]; simp
    nlinarith [Real.add_one_le_exp s, Real.exp_pos (-s)]
  have a : 1 / s ≤ 1 / (1 - Real.exp (-s)) :=
    one_div_le_one_div_of_le hd (by linarith [Real.add_one_le_exp (-s)])
  have b : 1 / (1 - Real.exp (-s)) - 1 / s ≤ 1 := by
    rw [div_sub_div _ _ hd.ne' hs.ne', div_le_one (by positivity)]; nlinarith
  unfold phiB; rw [abs_le]; constructor <;> linarith

theorem continuousOn_phiB : ContinuousOn phiB (Ioi 0) := by
  refine ((continuousOn_const.div (continuousOn_const.sub (Real.continuous_exp.comp
    continuous_neg).continuousOn) fun s hs => (one_sub_exp_neg_pos hs).ne').sub
    (continuousOn_const.div continuousOn_id fun s hs => (ne_of_gt hs))).sub continuousOn_const

theorem norm_cexp_neg_mul (z : ℂ) (s : ℝ) : ‖Complex.exp (-(z * s))‖ = Real.exp (-(z.re * s)) := by
  rw [Complex.norm_exp]; simp [Complex.mul_re]

/-- The Laplace transform `∫_0^∞ e^{−zs}φ(s) ds` is absolutely convergent, and `≤ 1/(2 Re z)`. -/
theorem integrableOn_lap {z : ℂ} (hz : 0 < z.re) :
    IntegrableOn (fun s : ℝ => Complex.exp (-(z * s)) * (phiB s : ℂ)) (Ioi 0) := by
  have he : IntegrableOn (fun s : ℝ => Real.exp (-(z.re * s))) (Ioi 0) := by
    simpa [neg_mul] using exp_neg_integrableOn_Ioi 0 hz
  have hb : IntegrableOn (fun s : ℝ => 1 / 2 * Real.exp (-(z.re * s))) (Ioi 0) := he.const_mul _
  refine hb.mono' ?_ ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun s hs => ?_))
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    exact ((Complex.continuous_exp.comp ((continuous_const.mul Complex.continuous_ofReal).neg)
      ).continuousOn).mul (Complex.continuous_ofReal.comp_continuousOn continuousOn_phiB)
  · rw [norm_mul, norm_cexp_neg_mul, Complex.norm_real, Real.norm_eq_abs, mul_comm]
    exact mul_le_mul_of_nonneg_right (abs_phiB_le hs) (Real.exp_pos _).le

theorem integral_exp_neg_mul' {c : ℝ} (hc : 0 < c) : ∫ s in Ioi (0 : ℝ), Real.exp (-(c * s)) = 1 / c := by
  have e : EqOn (fun t : ℝ => t ^ ((1 : ℝ) - 1) * Real.exp (-(c * t)))
      (fun t => Real.exp (-(c * t))) (Ioi 0) := fun t _ => by norm_num
  rw [← setIntegral_congr_fun measurableSet_Ioi e, Real.integral_rpow_mul_exp_neg_mul_Ioi one_pos hc,
    Real.rpow_one, Real.Gamma_one, mul_one]

theorem norm_lap_le {z : ℂ} (hz : 0 < z.re) :
    ‖∫ s in Ioi (0 : ℝ), Complex.exp (-(z * s)) * (phiB s : ℂ)‖ ≤ 1 / (2 * z.re) := by
  have he : IntegrableOn (fun s : ℝ => Real.exp (-(z.re * s))) (Ioi 0) := by
    simpa [neg_mul] using exp_neg_integrableOn_Ioi 0 hz
  have hb : IntegrableOn (fun s : ℝ => 1 / 2 * Real.exp (-(z.re * s))) (Ioi 0) := he.const_mul _
  refine (norm_integral_le_of_norm_le hb ((ae_restrict_iff' measurableSet_Ioi).2
    (Eventually.of_forall fun s hs => ?_))).trans_eq ?_
  · rw [norm_mul, norm_cexp_neg_mul, Complex.norm_real, Real.norm_eq_abs, mul_comm]
    exact mul_le_mul_of_nonneg_right (abs_phiB_le hs) (Real.exp_pos _).le
  · rw [integral_const_mul, integral_exp_neg_mul' hz]; field_simp

/-! ## C2. The complex Frullani integral -/

theorem segment_re_ge {z w : ℂ} {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    min z.re w.re ≤ (w + θ * (z - w)).re := by
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_re,
    Complex.sub_im, zero_mul, sub_zero]
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 (min_le_right z.re w.re)),
    mul_nonneg h0 (sub_nonneg.2 (min_le_left z.re w.re))]

/-- `(e^{−ws} − e^{−zs})/s = ∫_0^1 (z − w)e^{−(w + θ(z − w))s} dθ`. -/
theorem frullani_inner (z w : ℂ) {s : ℝ} (hs : 0 < s) :
    (Complex.exp (-(w * s)) - Complex.exp (-(z * s))) / s
      = ∫ θ in (0 : ℝ)..1, (z - w) * Complex.exp (-((w + θ * (z - w)) * s)) := by
  have hs' : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hs.ne'
  have hd : ∀ θ : ℝ, HasDerivAt (fun θ : ℝ => -Complex.exp (-((w + θ * (z - w)) * s)) / s)
      ((z - w) * Complex.exp (-((w + θ * (z - w)) * s))) θ := fun θ => by
    have h1 : HasDerivAt (fun θ : ℝ => (θ : ℂ)) 1 θ := (hasDerivAt_id θ).ofReal_comp
    have h2 := (((h1.mul_const (z - w)).const_add w).mul_const (s : ℂ)).fun_neg.cexp.fun_neg.div_const
      (s : ℂ)
    convert h2 using 1; field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun θ _ => hd θ)
    (Continuous.intervalIntegrable (by fun_prop) _ _)]
  simp only [Complex.ofReal_one, Complex.ofReal_zero, one_mul, zero_mul, add_zero,
    add_sub_cancel]
  ring

theorem integrable_frullani_prod {z w : ℂ} (hz : 0 < z.re) (hw : 0 < w.re) :
    Integrable (Function.uncurry fun (s θ : ℝ) => (z - w) * Complex.exp (-((w + θ * (z - w)) * s)))
      ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioc 0 1))) := by
  set σ := min z.re w.re
  have hσ : 0 < σ := lt_min hz hw
  have hb : Integrable (fun p : ℝ × ℝ => (‖z - w‖ * Real.exp (-(σ * p.1))) * (1 : ℝ))
      ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioc 0 1))) :=
    Integrable.mul_prod (f := fun s : ℝ => ‖z - w‖ * Real.exp (-(σ * s))) (g := fun _ : ℝ => (1 : ℝ))
      ((by simpa [neg_mul] using exp_neg_integrableOn_Ioi 0 hσ : IntegrableOn
        (fun s : ℝ => Real.exp (-(σ * s))) (Ioi 0)).const_mul _)
      (integrable_const _)
  refine hb.mono' (Continuous.aestronglyMeasurable (by fun_prop)) ?_
  rw [Measure.prod_restrict]
  refine (ae_restrict_iff' (measurableSet_Ioi.prod measurableSet_Ioc)).2
    (Eventually.of_forall fun p hp => ?_)
  obtain ⟨hs, hθ⟩ := hp
  have hs' : 0 < p.1 := hs
  show ‖(z - w) * Complex.exp (-((w + (p.2 : ℂ) * (z - w)) * p.1))‖ ≤ ‖z - w‖ * Real.exp (-(σ * p.1)) * 1
  rw [mul_one, norm_mul, norm_cexp_neg_mul]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by
    have := segment_re_ge (z := z) (w := w) hθ.1.le hθ.2; nlinarith)) (norm_nonneg _)

/-- **The complex Frullani integral**: `∫_0^∞ (e^{−ws} − e^{−zs})/s ds = log z − log w`. -/
theorem integral_frullani {z w : ℂ} (hz : 0 < z.re) (hw : 0 < w.re) :
    ∫ s in Ioi (0 : ℝ), (Complex.exp (-(w * s)) - Complex.exp (-(z * s))) / s
      = Complex.log z - Complex.log w := by
  set σ := min z.re w.re
  have hσ : 0 < σ := lt_min hz hw
  have hre : ∀ θ : ℝ, θ ∈ Set.uIcc (0 : ℝ) 1 → 0 < (w + θ * (z - w)).re := fun θ hθ => by
    rw [Set.uIcc_of_le zero_le_one] at hθ
    exact hσ.trans_le (segment_re_ge hθ.1 hθ.2)
  rw [setIntegral_congr_fun measurableSet_Ioi fun s hs => frullani_inner z w hs]
  simp_rw [intervalIntegral.integral_of_le zero_le_one]
  rw [integral_integral_swap (integrable_frullani_prod hz hw)]
  have hin : ∀ θ ∈ Ioc (0 : ℝ) 1, ∫ s in Ioi (0 : ℝ), (z - w) * Complex.exp (-((w + θ * (z - w)) * s))
      = (z - w) / (w + θ * (z - w)) := fun θ hθ => by
    have hθ' : θ ∈ Set.uIcc (0 : ℝ) 1 := by
      rw [Set.uIcc_of_le zero_le_one]; exact Ioc_subset_Icc_self hθ
    rw [integral_const_mul, integral_cexp_neg (hre θ hθ')]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioc hin, ← intervalIntegral.integral_of_le zero_le_one]
  have hd : ∀ θ ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt (fun θ : ℝ => Complex.log (w + θ * (z - w)))
      ((z - w) / (w + θ * (z - w))) θ := fun θ hθ => by
    have h1 : HasDerivAt (fun θ : ℝ => (θ : ℂ)) 1 θ := (hasDerivAt_id θ).ofReal_comp
    have h2 := ((h1.mul_const (z - w)).const_add w).clog_real
      (Complex.mem_slitPlane_iff.2 (Or.inl (hre θ hθ)))
    simpa using h2
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (ContinuousOn.intervalIntegrable ?_)]
  · simp
  · refine ContinuousOn.div continuousOn_const (Continuous.continuousOn (by fun_prop)) fun θ hθ => ?_
    intro h; have := hre θ hθ; rw [h, Complex.zero_re] at this; exact lt_irrefl _ this


/-! ## C3. `ψ` as a Laplace transform -/

/-- `L(z) = ∫_0^∞ e^{−zs}φ(s) ds`. -/
def lap (z : ℂ) : ℂ := ∫ s in Ioi (0 : ℝ), Complex.exp (-(z * s)) * (phiB s : ℂ)

theorem integrableOn_frullani {z w : ℂ} (hz : 0 < z.re) (hw : 0 < w.re) :
    IntegrableOn (fun s : ℝ => (Complex.exp (-(w * s)) - Complex.exp (-(z * s))) / s) (Ioi 0) := by
  set σ := min z.re w.re
  have hσ : 0 < σ := lt_min hz hw
  have he : IntegrableOn (fun s : ℝ => Real.exp (-(σ * s))) (Ioi 0) := by
    simpa [neg_mul] using exp_neg_integrableOn_Ioi 0 hσ
  refine (he.const_mul ‖z - w‖).mono' ?_
    ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun s hs => ?_))
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    refine ContinuousOn.div (Continuous.continuousOn (by fun_prop))
      Complex.continuous_ofReal.continuousOn fun s hs => ?_
    exact Complex.ofReal_ne_zero.2 (ne_of_gt hs)
  · have hs' : 0 < s := hs
    have hD := norm_cexp_sub_le (min_le_left z.re w.re) (min_le_right z.re w.re) hs'.le
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hs'.le, div_le_iff₀ hs']
    calc _ ≤ ‖z - w‖ * (s * Real.exp (-(σ * s))) := hD
      _ = _ := by ring

theorem K_const {z w : ℂ} (hz : 0 < z.re) (hw : 0 < w.re) :
    Complex.digamma z - Complex.log z + 1 / (2 * z) + lap z
      = Complex.digamma w - Complex.log w + 1 / (2 * w) + lap w := by
  have hG := (digamma_sub_eq_integral hz hw).2
  have hF := integral_frullani hz hw
  have I1 := integrableOn_gaussK hz hw
  have I2 := integrableOn_frullani hz hw
  have I3 : IntegrableOn (fun s : ℝ => (Complex.exp (-(z * s)) - Complex.exp (-(w * s))) / 2) (Ioi 0) :=
    ((integrableOn_cexp_neg hz).sub (integrableOn_cexp_neg hw)).div_const 2
  have hC : ∫ s in Ioi (0 : ℝ), (Complex.exp (-(z * s)) - Complex.exp (-(w * s))) / 2
      = (1 / z - 1 / w) / 2 := by
    rw [integral_div, integral_sub (integrableOn_cexp_neg hz) (integrableOn_cexp_neg hw),
      integral_cexp_neg hz, integral_cexp_neg hw]
  have hpt : EqOn (fun s : ℝ => gaussK z w s - (Complex.exp (-(w * s)) - Complex.exp (-(z * s))) / s
        + (Complex.exp (-(z * s)) - Complex.exp (-(w * s))) / 2)
      (fun s : ℝ => Complex.exp (-(w * s)) * (phiB s : ℂ) - Complex.exp (-(z * s)) * (phiB s : ℂ))
      (Ioi 0) := fun s _ => by
    simp only [gaussK, phiB]; push_cast; ring
  have e := setIntegral_congr_fun (μ := volume) measurableSet_Ioi hpt
  have a1 : (∫ s in Ioi (0 : ℝ), (gaussK z w s - (Complex.exp (-(w * s)) - Complex.exp (-(z * s))) / s
        + (Complex.exp (-(z * s)) - Complex.exp (-(w * s))) / 2))
      = (∫ s in Ioi (0 : ℝ), (gaussK z w s - (Complex.exp (-(w * s)) - Complex.exp (-(z * s))) / s))
        + ∫ s in Ioi (0 : ℝ), (Complex.exp (-(z * s)) - Complex.exp (-(w * s))) / 2 :=
    integral_add (I1.sub I2) I3
  have a2 : (∫ s in Ioi (0 : ℝ), (gaussK z w s - (Complex.exp (-(w * s)) - Complex.exp (-(z * s))) / s))
      = (∫ s in Ioi (0 : ℝ), gaussK z w s)
        - ∫ s in Ioi (0 : ℝ), (Complex.exp (-(w * s)) - Complex.exp (-(z * s))) / s :=
    integral_sub I1 I2
  have a3 : (∫ s in Ioi (0 : ℝ), (Complex.exp (-(w * s)) * (phiB s : ℂ)
        - Complex.exp (-(z * s)) * (phiB s : ℂ)))
      = lap w - lap z := integral_sub (integrableOn_lap hw) (integrableOn_lap hz)
  rw [a1, a2, a3, ← hG, hF, hC] at e
  linear_combination e

theorem tendsto_K_nat :
    Tendsto (fun m : ℕ => Complex.digamma ((m : ℂ) + 1) - Complex.log ((m : ℂ) + 1)
      + 1 / (2 * ((m : ℂ) + 1)) + lap ((m : ℂ) + 1)) atTop (𝓝 0) := by
  have hre : ∀ m : ℕ, ((m : ℂ) + 1).re = (m : ℝ) + 1 := fun m => by simp
  have T0 : Tendsto (fun m : ℕ => (1 : ℝ) / (2 * ((m : ℝ) + 1))) atTop (𝓝 0) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul (1 / 2 : ℝ)
    rw [mul_zero] at this
    exact this.congr fun m => by field_simp
  have T1 : Tendsto (fun m : ℕ => ((((harmonic m : ℚ) : ℝ) - Real.log ((m : ℝ) + 1)
      - Real.eulerMascheroniConstant : ℝ) : ℂ)) atTop (𝓝 0) := by
    have h := (Real.tendsto_harmonic_sub_log_add_one.sub_const Real.eulerMascheroniConstant)
    rw [sub_self] at h
    have := (Complex.continuous_ofReal.tendsto 0).comp h
    rwa [Complex.ofReal_zero] at this
  have T2 : Tendsto (fun m : ℕ => (((1 : ℝ) / (2 * ((m : ℝ) + 1)) : ℝ) : ℂ)) atTop (𝓝 0) := by
    have := (Complex.continuous_ofReal.tendsto 0).comp T0
    rwa [Complex.ofReal_zero] at this
  have T3 : Tendsto (fun m : ℕ => lap ((m : ℂ) + 1)) atTop (𝓝 0) :=
    squeeze_zero_norm (fun m => by
      have := norm_lap_le (z := (m : ℂ) + 1) (by rw [hre]; positivity)
      rwa [hre] at this) T0
  have := (T1.add T2).add T3
  rw [add_zero, add_zero] at this
  refine this.congr fun m => ?_
  have hl : Complex.log ((m : ℂ) + 1) = ((Real.log ((m : ℝ) + 1) : ℝ) : ℂ) := by
    rw [Complex.ofReal_log (by positivity)]; push_cast; rfl
  rw [Complex.digamma_nat_add_one, hl]
  push_cast; ring

/-- **`ψ` as a Laplace transform**: `ψ(z) = log z − 1/(2z) − ∫_0^∞ e^{−zs}φ(s) ds` for `Re z > 0`. -/
theorem digamma_eq_lap {z : ℂ} (hz : 0 < z.re) :
    Complex.digamma z = Complex.log z - 1 / (2 * z) - lap z := by
  have hK : Tendsto (fun _ : ℕ => Complex.digamma z - Complex.log z + 1 / (2 * z) + lap z) atTop
      (𝓝 0) :=
    tendsto_K_nat.congr fun m => (K_const hz (by simp; positivity)).symm
  have := tendsto_nhds_unique tendsto_const_nhds hK
  linear_combination this


/-! ## D. `φ` as a sine transform -/

/-- `∫_0^∞ sin(st)e^{−ct} dt = s/(s² + c²)`. -/
theorem integral_sin_mul_exp {s c : ℝ} (hc : 0 < c) :
    ∫ t in Ioi (0 : ℝ), Real.sin (s * t) * Real.exp (-(c * t)) = s / (s ^ 2 + c ^ 2) := by
  have hre : 0 < ((c : ℂ) - s * Complex.I).re := by simpa using hc
  have h : ∀ t : ℝ, Real.sin (s * t) * Real.exp (-(c * t))
      = (Complex.exp (-(((c : ℂ) - s * Complex.I) * t))).im := fun t => by
    rw [Complex.exp_im]
    simp [Complex.mul_re, Complex.mul_im]
    ring
  simp_rw [h]
  have hi := Complex.imCLM.integral_comp_comm (integrableOn_cexp_neg hre)
  simp only [Complex.imCLM_apply] at hi
  rw [hi, integral_cexp_neg hre]
  have hn : ((c : ℂ) - s * Complex.I) ≠ 0 := fun h0 => by
    rw [h0, Complex.zero_re] at hre; exact lt_irrefl _ hre
  rw [one_div, Complex.inv_im, Complex.normSq_apply]
  simp
  ring

theorem abs_sin_mul_le {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) : |Real.sin (s * t)| ≤ s * t :=
  (Real.abs_sin_le_abs).trans (abs_of_nonneg (mul_nonneg hs ht)).le

/-- The Mittag-Leffler expansion: `φ(s) = Σ_{n≥1} 2s/(s² + 4π²n²)`. -/
theorem hasSum_phiB {s : ℝ} (hs : 0 < s) :
    HasSum (fun n : ℕ => 2 * s / (s ^ 2 + (2 * π * ((n : ℝ) + 1)) ^ 2)) (phiB s) := by
  set x : ℂ := (s : ℂ) * Complex.I / (2 * π)
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  have hs0 : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hs.ne'
  have hxim : x.im = s / (2 * π) := by
    simp only [x]; rw [Complex.div_im]; simp [Complex.normSq]; field_simp
  have hx : x ∈ Complex.integerComplement := by
    rw [Complex.mem_integerComplement_iff]
    rintro ⟨n, hn⟩
    have := congrArg Complex.im hn
    rw [hxim, Complex.intCast_im] at this
    have : 0 < s / (2 * π) := by positivity
    linarith
  have H := ((Summable.hasSum_iff_tendsto_nat (summable_cotTerm hx)).mpr
    (tendsto_logDeriv_euler_cot_sub hx)).mul_left (Complex.I / (2 * π))
  rw [← Complex.hasSum_ofReal]
  convert H using 1
  · funext n
    set m : ℂ := (n : ℂ) + 1
    have h3 : (s : ℂ) ^ 2 + (2 * π * m) ^ 2 ≠ 0 := by
      simp only [m]
      exact_mod_cast (by positivity : (0 : ℝ) < s ^ 2 + (2 * π * ((n : ℝ) + 1)) ^ 2).ne'
    have hxx : x ^ 2 = -(s : ℂ) ^ 2 / (4 * π ^ 2) := by
      simp only [x]; rw [div_pow, mul_pow, Complex.I_sq]; ring
    have hIx : Complex.I / (2 * π) * x = -(s : ℂ) / (4 * π ^ 2) := by
      simp only [x]
      rw [show Complex.I / (2 * π) * ((s : ℂ) * Complex.I / (2 * π))
        = (s : ℂ) * (Complex.I * Complex.I) / (4 * π ^ 2) by ring, Complex.I_mul_I]
      ring
    have hden : x ^ 2 - m ^ 2 = -((s : ℂ) ^ 2 + (2 * π * m) ^ 2) / (4 * π ^ 2) := by
      rw [hxx]; field_simp; ring
    have e1 : Complex.I / (2 * π) * cotTerm x n = 2 * (Complex.I / (2 * π) * x) / (x ^ 2 - m ^ 2) := by
      rw [cotTerm_identity hx n, show (x + ((n : ℂ) + 1)) * (x - ((n : ℂ) + 1)) = x ^ 2 - m ^ 2 by
        simp only [m]; ring]
      ring
    rw [e1, hIx, hden]
    push_cast
    field_simp
    rfl
  · have hc : Complex.cot (π * x)
        = (Complex.exp (-(s : ℂ)) + 1) / (Complex.I * (1 - Complex.exp (-(s : ℂ)))) := by
      rw [Complex.cot_eq_exp_ratio]
      have : 2 * Complex.I * (π * x) = -(s : ℂ) := by
        simp only [x]
        rw [show 2 * Complex.I * (π * ((s : ℂ) * Complex.I / (2 * π)))
          = (s : ℂ) * (Complex.I * Complex.I) * (π / π) by ring, Complex.I_mul_I, div_self hπ]
        ring
      rw [this]
    have hd : (1 : ℂ) - Complex.exp (-(s : ℂ)) ≠ 0 := by
      rw [show Complex.exp (-(s : ℂ)) = ((Real.exp (-s) : ℝ) : ℂ) by push_cast; rfl]
      exact_mod_cast (one_sub_exp_neg_pos hs).ne'
    have hI : Complex.I ≠ 0 := Complex.I_ne_zero
    rw [hc]
    simp only [phiB, x]
    push_cast
    field_simp
    ring_nf

/-- `1/(e^{2πt} − 1) = Σ_{n≥0} e^{−2π(n+1)t}` for `t > 0`. -/
theorem hasSum_bose {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℕ => Real.exp (-((2 * π * ((n : ℝ) + 1)) * t)))
      (1 / (Real.exp (2 * π * t) - 1)) := by
  set ξ := Real.exp (-(2 * π * t))
  have hξ0 : 0 ≤ ξ := (Real.exp_pos _).le
  have hξ1 : ξ < 1 := Real.exp_lt_one_iff.2 (by nlinarith [Real.pi_pos])
  have h := (hasSum_geometric_of_lt_one hξ0 hξ1).mul_left ξ
  have e1 : ∀ n : ℕ, ξ * ξ ^ n = Real.exp (-((2 * π * ((n : ℝ) + 1)) * t)) := fun n => by
    rw [← pow_succ', ← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hE : Real.exp (2 * π * t) * ξ = 1 := by rw [← Real.exp_add]; simp
  have hden : 0 < Real.exp (2 * π * t) - 1 := by
    have := Real.add_one_le_exp (2 * π * t); nlinarith [Real.pi_pos]
  have e2 : ξ * (1 - ξ)⁻¹ = 1 / (Real.exp (2 * π * t) - 1) := by
    have h1ξ : 1 - ξ ≠ 0 := by linarith
    rw [eq_div_iff hden.ne', mul_assoc, mul_comm _ (Real.exp (2 * π * t) - 1), ← mul_assoc,
      mul_inv_eq_iff_eq_mul₀ h1ξ]
    linear_combination hE
  convert h using 1
  · funext n; exact (e1 n).symm
  · exact e2.symm

/-- **`φ` as a sine transform**: `φ(s) = 2∫_0^∞ sin(st)/(e^{2πt} − 1) dt`. -/
theorem phiB_eq_sine {s : ℝ} (hs : 0 < s) :
    phiB s = 2 * ∫ t in Ioi (0 : ℝ), Real.sin (s * t) / (Real.exp (2 * π * t) - 1) := by
  set c : ℕ → ℝ := fun n => 2 * π * ((n : ℝ) + 1)
  have hc : ∀ n, 0 < c n := fun n => by positivity
  set F : ℕ → ℝ → ℝ := fun n t => Real.sin (s * t) * Real.exp (-(c n * t))
  have hFint : ∀ n, Integrable (F n) (volume.restrict (Ioi 0)) := fun n => by
    have he : IntegrableOn (fun t : ℝ => Real.exp (-(c n * t))) (Ioi 0) := by
      simpa [neg_mul] using exp_neg_integrableOn_Ioi 0 (hc n)
    refine he.mono' (Continuous.aestronglyMeasurable (by fun_prop)) (Eventually.of_forall fun t => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_of_le_one_left (Real.exp_pos _).le (Real.abs_sin_le_one _)
  have hFnorm : ∀ n, ∫ t in Ioi (0 : ℝ), ‖F n t‖ ≤ s / c n ^ 2 := fun n => by
    calc ∫ t in Ioi (0 : ℝ), ‖F n t‖ ≤ ∫ t in Ioi (0 : ℝ), s * (t * Real.exp (-(c n * t))) :=
          integral_mono_of_nonneg (Eventually.of_forall fun t => norm_nonneg _)
            ((integrableOn_mul_exp_neg (hc n)).const_mul s)
            ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => by
              have ht' : 0 < t := ht
              show ‖Real.sin (s * t) * Real.exp (-(c n * t))‖ ≤ s * (t * Real.exp (-(c n * t)))
              rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
              have := abs_sin_mul_le hs.le ht'.le
              nlinarith [Real.exp_pos (-(c n * t))]))
      _ = s / c n ^ 2 := by rw [integral_const_mul, integral_mul_exp_neg (hc n)]; ring
  have hsum : Summable fun n => ∫ t in Ioi (0 : ℝ), ‖F n t‖ := by
    refine Summable.of_nonneg_of_le (fun n => integral_nonneg fun t => norm_nonneg _) hFnorm ?_
    refine (summable_inv_sq.mul_left (s / (4 * π ^ 2))).congr fun n => ?_
    simp only [c]; field_simp; ring
  have H := hasSum_integral_of_summable_integral_norm hFint hsum
  have hval : (fun n => ∫ t in Ioi (0 : ℝ), F n t) = fun n => s / (s ^ 2 + c n ^ 2) :=
    funext fun n => integral_sin_mul_exp (hc n)
  rw [hval] at H
  have hcong : ∫ t in Ioi (0 : ℝ), ∑' n, F n t
      = ∫ t in Ioi (0 : ℝ), Real.sin (s * t) / (Real.exp (2 * π * t) - 1) :=
    setIntegral_congr_fun measurableSet_Ioi fun t ht => by
      simp only [F, c]
      rw [tsum_mul_left, (hasSum_bose ht).tsum_eq]
      ring
  rw [hcong] at H
  refine (hasSum_phiB hs).unique ?_
  convert H.mul_left 2 using 1
  funext n; simp only [c]; ring

/-! ## E. Fubini -/

theorem bose_le' {t : ℝ} (ht : 0 < t) :
    t / (Real.exp (2 * π * t) - 1) ≤ Real.exp (-(π * t)) / (2 * π) := by
  have hx : 0 < π * t := by positivity
  have hsinh : π * t ≤ Real.sinh (π * t) := Real.self_le_sinh_iff.2 hx.le
  have hden : 0 < Real.exp (2 * π * t) - 1 := by
    have h1 := Real.add_one_le_exp (2 * π * t)
    have h2 : 0 < 2 * π * t := by positivity
    linarith
  rw [div_le_div_iff₀ hden (by positivity)]
  have e : Real.exp (-(π * t)) * (Real.exp (2 * π * t) - 1) = 2 * Real.sinh (π * t) := by
    rw [Real.sinh_eq, mul_sub, ← Real.exp_add, mul_one,
      show -(π * t) + 2 * π * t = π * t by ring]
    ring
  rw [e]
  nlinarith [Real.pi_pos]

/-- `∫_0^∞ e^{−zs} sin(st) ds = t/(z² + t²)`. -/
theorem integral_exp_mul_sin {z : ℂ} (hz : 0 < z.re) (t : ℝ) :
    ∫ s in Ioi (0 : ℝ), Complex.exp (-(z * s)) * (Real.sin (s * t) : ℂ) = t / (z ^ 2 + t ^ 2) := by
  have h1 : 0 < (z - t * Complex.I).re := by simpa using hz
  have h2 : 0 < (z + t * Complex.I).re := by simpa using hz
  have hpt : ∀ s : ℝ, Complex.exp (-(z * s)) * (Real.sin (s * t) : ℂ)
      = (Complex.exp (-((z - t * Complex.I) * s)) - Complex.exp (-((z + t * Complex.I) * s)))
        * (-Complex.I / 2) := fun s => by
    rw [Complex.ofReal_sin, Complex.sin]
    rw [show -((z - t * Complex.I) * s) = -(z * s) + ((s : ℂ) * t) * Complex.I by ring,
      show -((z + t * Complex.I) * s) = -(z * s) + -(((s : ℂ) * t) * Complex.I) by ring,
      Complex.exp_add, Complex.exp_add]
    push_cast
    ring_nf
  simp_rw [hpt]
  rw [integral_mul_const, integral_sub (integrableOn_cexp_neg h1) (integrableOn_cexp_neg h2),
    integral_cexp_neg h1, integral_cexp_neg h2]
  have n1 : z - t * Complex.I ≠ 0 := fun h => by rw [h, Complex.zero_re] at h1; exact lt_irrefl _ h1
  have n2 : z + t * Complex.I ≠ 0 := fun h => by rw [h, Complex.zero_re] at h2; exact lt_irrefl _ h2
  have hf : z ^ 2 + (t : ℂ) ^ 2 = (z - t * Complex.I) * (z + t * Complex.I) := by
    ring_nf; rw [Complex.I_sq]; ring
  rw [hf]
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring

theorem integrable_binet_prod {z : ℂ} (hz : 0 < z.re) :
    Integrable (Function.uncurry fun (s t : ℝ) =>
        Complex.exp (-(z * s)) * ((Real.sin (s * t) / (Real.exp (2 * π * t) - 1) : ℝ) : ℂ))
      ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))) := by
  have he : IntegrableOn (fun t : ℝ => Real.exp (-(π * t))) (Ioi 0) := by
    simpa [neg_mul] using exp_neg_integrableOn_Ioi 0 Real.pi_pos
  have hb : Integrable (fun p : ℝ × ℝ => (p.1 * Real.exp (-(z.re * p.1))) * (Real.exp (-(π * p.2)) / (2 * π)))
      ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))) :=
    Integrable.mul_prod (f := fun s : ℝ => s * Real.exp (-(z.re * s)))
      (g := fun t : ℝ => Real.exp (-(π * t)) / (2 * π)) (integrableOn_mul_exp_neg hz) (he.div_const _)
  refine hb.mono' (Measurable.aestronglyMeasurable (by fun_prop)) ?_
  rw [Measure.prod_restrict]
  refine (ae_restrict_iff' (measurableSet_Ioi.prod measurableSet_Ioi)).2
    (Eventually.of_forall fun p hp => ?_)
  obtain ⟨hs, ht⟩ := hp
  have hs' : 0 < p.1 := hs
  have ht' : 0 < p.2 := ht
  have hden : 0 < Real.exp (2 * π * p.2) - 1 := by
    have := Real.add_one_le_exp (2 * π * p.2); nlinarith [Real.pi_pos]
  show ‖Complex.exp (-(z * p.1)) * ((Real.sin (p.1 * p.2) / (Real.exp (2 * π * p.2) - 1) : ℝ) : ℂ)‖
    ≤ (p.1 * Real.exp (-(z.re * p.1))) * (Real.exp (-(π * p.2)) / (2 * π))
  rw [norm_mul, norm_cexp_neg_mul, Complex.norm_real, Real.norm_eq_abs, abs_div,
    abs_of_pos hden]
  have h1 := abs_sin_mul_le hs'.le ht'.le
  have h2 := bose_le' ht'
  have h3 : |Real.sin (p.1 * p.2)| / (Real.exp (2 * π * p.2) - 1)
      ≤ p.1 * (Real.exp (-(π * p.2)) / (2 * π)) := by
    calc |Real.sin (p.1 * p.2)| / (Real.exp (2 * π * p.2) - 1)
        ≤ p.1 * p.2 / (Real.exp (2 * π * p.2) - 1) := div_le_div_of_nonneg_right h1 hden.le
      _ = p.1 * (p.2 / (Real.exp (2 * π * p.2) - 1)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h2 hs'.le
  calc Real.exp (-(z.re * p.1)) * (|Real.sin (p.1 * p.2)| / (Real.exp (2 * π * p.2) - 1))
      ≤ Real.exp (-(z.re * p.1)) * (p.1 * (Real.exp (-(π * p.2)) / (2 * π))) :=
        mul_le_mul_of_nonneg_left h3 (Real.exp_pos _).le
    _ = _ := by ring

/-- `∫_0^∞ e^{−zs}φ(s) ds = 2∫_0^∞ t dt/((t² + z²)(e^{2πt} − 1))`. -/
theorem lap_eq {z : ℂ} (hz : 0 < z.re) :
    lap z = 2 * ∫ t in Ioi (0 : ℝ),
      (t : ℂ) / (((t : ℂ) ^ 2 + z ^ 2) * ((Real.exp (2 * π * t) - 1 : ℝ) : ℂ)) := by
  set G : ℝ → ℝ → ℂ := fun s t =>
    Complex.exp (-(z * s)) * ((Real.sin (s * t) / (Real.exp (2 * π * t) - 1) : ℝ) : ℂ)
  have hin : ∀ s ∈ Ioi (0 : ℝ), Complex.exp (-(z * s)) * (phiB s : ℂ)
      = 2 * ∫ t in Ioi (0 : ℝ), G s t := fun s hs => by
    rw [phiB_eq_sine hs, Complex.ofReal_mul, ← integral_complex_ofReal]
    simp only [G]
    rw [integral_const_mul]
    push_cast; ring
  unfold lap
  rw [setIntegral_congr_fun measurableSet_Ioi hin, integral_const_mul,
    integral_integral_swap (integrable_binet_prod hz)]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have e : ∀ s : ℝ, G s t = Complex.exp (-(z * s)) * (Real.sin (s * t) : ℂ)
      * (((1 / (Real.exp (2 * π * t) - 1)) : ℝ) : ℂ) := fun s => by
    show Complex.exp (-(z * s)) * ((Real.sin (s * t) / (Real.exp (2 * π * t) - 1) : ℝ) : ℂ) = _
    push_cast; ring
  refine (integral_congr_ae (Eventually.of_forall e)).trans ?_
  rw [integral_mul_const, integral_exp_mul_sin hz t, Complex.ofReal_div, Complex.ofReal_one,
    div_mul_div_comm, mul_one, add_comm (z ^ 2)]

/-- **Binet's second formula**: for `Re z > 0`,
`ψ(z) = log z − 1/(2z) − 2∫_0^∞ t dt/((t² + z²)(e^{2πt} − 1))`. -/
theorem binet {z : ℂ} (hz : 0 < z.re) :
    Complex.digamma z = Complex.log z - 1 / (2 * z)
      - 2 * ∫ t in Ioi (0 : ℝ),
        (t : ℂ) / (((t : ℂ) ^ 2 + z ^ 2) * ((Real.exp (2 * π * t) - 1 : ℝ) : ℂ)) := by
  rw [digamma_eq_lap hz, lap_eq hz]

end PilotDigamma

#print axioms PilotDigamma.integral_frullani
#print axioms PilotDigamma.digamma_eq_lap
#print axioms PilotDigamma.hasSum_phiB
#print axioms PilotDigamma.phiB_eq_sine
#print axioms PilotDigamma.integral_exp_mul_sin
#print axioms PilotDigamma.lap_eq
#print axioms PilotDigamma.binet
