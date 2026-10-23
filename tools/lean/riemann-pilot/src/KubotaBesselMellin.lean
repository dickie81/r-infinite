import KubotaExpansion

/-! # The Mellin transform of `K_ν` (round 372)

S5f-4a, the first part of round 360's S5f-4 (the Mellin side). The companion paper writes: "`For each
nonzero Fourier mode, differentiation and the Mellin integral for $K_{1/3}$ (see \cite[(10.43.19)]{DLMF})
give the following formulas:`", the second of which is its (A.15). This file proves (A.15) from round 361's
`K_ν(x) = ½∫_0^∞ t^{ν−1}e^{−x(t+1/t)/2} dt`.

* **The Beta integral of the second kind** (`integral_beta2`): `∫_0^∞ u^{p−1}(1 + u)^{−(p+q)} du = B(p, q)`,
  from Mathlib's `betaIntegral` by `x = u/(1 + u)`. As an identity of integrals it needs no condition on
  `p, q`.
* **`∫_0^∞ t^{a−1}(1 + t²)^{−w} dt = ½B(a/2, w − a/2)`** (`integral_one_add_sq`), by `u = t²`.
* **The inner integral** (`integral_bkK`): `∫_0^∞ v^{w−1}e^{−v(t+1/t)/2} dv = 2^w t^w(1 + t²)^{−w}Γ(w)`.
* **`mellin_besselK`**: `∫_0^∞ v^{w−1}K_ν(v) dv = 2^{w−2}Γ((w−ν)/2)Γ((w+ν)/2)` for `|Re ν| < Re w`, by Fubini
  on `(0, ∞)²`. The integrability comes from the inner integral and the majorant
  `t^{a−1}(2t/(1 + t²))^b`, integrable for `|a| < b` (`integrableOn_bk_majorant`).
* **(A.15)** (`integral_besselK_third`): `∫_0^∞ v^{2s}K_{1/3}(av) dv = 2^{2s−1}Γ(s + 1/3)Γ(s + 2/3)a^{−(2s+1)}`
  for `a > 0` and `Re s > −1/3`.
-/

open Real Set Filter MeasureTheory Complex
open scoped Topology

noncomputable section

namespace Eis

/-- `u ↦ u/(1 + u)` maps `(0, ∞)` onto `(0, 1)`. -/
theorem image_div_one_add : (fun u : ℝ => u / (1 + u)) '' Ioi 0 = Ioo 0 1 := by
  ext x
  simp only [mem_image, mem_Ioi, mem_Ioo]
  constructor
  · rintro ⟨u, hu, rfl⟩
    refine ⟨by positivity, ?_⟩
    rw [div_lt_one (by positivity)]; linarith
  · rintro ⟨h0, h1⟩
    refine ⟨x / (1 - x), div_pos h0 (by linarith), ?_⟩
    have h1' : (1 - x) ≠ 0 := by linarith
    field_simp
    ring

theorem cpow_ofReal_div_one_add {u : ℝ} (hu : 0 < u) (r : ℂ) :
    (((u / (1 + u) : ℝ)) : ℂ) ^ r = (u : ℂ) ^ r * (((1 + u : ℝ)) : ℂ) ^ (-r) := by
  have h1 : (0 : ℝ) < 1 + u := by linarith
  rw [div_eq_mul_inv, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hu.le (inv_nonneg.2 h1.le),
    Complex.ofReal_inv, Complex.inv_cpow _ _ (by rw [Complex.arg_ofReal_of_nonneg h1.le]; exact Real.pi_pos.ne),
    Complex.cpow_neg]

/-- **The Beta integral of the second kind**: `∫_0^∞ u^{p−1}(1 + u)^{−(p+q)} du = B(p, q)` for
`Re p, Re q > 0`. -/
theorem integral_beta2 (p q : ℂ) :
    ∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (p - 1) * (((1 + u : ℝ)) : ℂ) ^ (-(p + q)) = betaIntegral p q := by
  have hderiv : ∀ u ∈ Ioi (0 : ℝ), HasDerivWithinAt (fun u : ℝ => u / (1 + u)) (1 / (1 + u) ^ 2) (Ioi 0) u := by
    intro u hu
    have h1 : (1 + u) ≠ 0 := by have := mem_Ioi.1 hu; linarith
    have h := (hasDerivAt_id' u).div ((hasDerivAt_id' u).const_add 1) h1
    rw [show (1 * (1 + u) - u * 1) / (1 + u) ^ 2 = 1 / (1 + u) ^ 2 by ring] at h
    exact h.hasDerivWithinAt
  have hinj : InjOn (fun u : ℝ => u / (1 + u)) (Ioi 0) := by
    intro a ha b hb hab
    simp only at hab
    have ha' : (1 + a) ≠ 0 := by have := mem_Ioi.1 ha; linarith
    have hb' : (1 + b) ≠ 0 := by have := mem_Ioi.1 hb; linarith
    field_simp at hab
    linarith
  have key := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hderiv hinj
    (fun x : ℝ => (x : ℂ) ^ (p - 1) * ((1 - x : ℝ) : ℂ) ^ (q - 1))
  rw [image_div_one_add] at key
  rw [betaIntegral, intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
  have e1 : ∫ x in Ioo (0 : ℝ) 1, (x : ℂ) ^ (p - 1) * (1 - (x : ℂ)) ^ (q - 1) =
      ∫ x in Ioo (0 : ℝ) 1, (x : ℂ) ^ (p - 1) * ((1 - x : ℝ) : ℂ) ^ (q - 1) := by
    refine setIntegral_congr_fun measurableSet_Ioo fun x _ => ?_
    push_cast; rfl
  rw [e1, key]
  refine (setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_).symm
  have hu' : 0 < u := hu
  have h1 : (0 : ℝ) < 1 + u := by linarith
  have h1c : (((1 + u : ℝ)) : ℂ) ≠ 0 := by exact_mod_cast h1.ne'
  have e2 : (1 - u / (1 + u) : ℝ) = (1 + u)⁻¹ := by field_simp; ring
  rw [e2, cpow_ofReal_div_one_add hu', abs_of_pos (by positivity), Complex.real_smul,
    Complex.ofReal_inv, Complex.inv_cpow _ _ (by rw [Complex.arg_ofReal_of_nonneg h1.le]; exact Real.pi_pos.ne),
    ← Complex.cpow_neg]
  have e3 : (((1 / (1 + u) ^ 2 : ℝ)) : ℂ) = (((1 + u : ℝ)) : ℂ) ^ (-(2 : ℂ)) := by
    rw [Complex.cpow_neg, show (2 : ℂ) = ((2 : ℕ) : ℂ) by norm_num, Complex.cpow_natCast]
    push_cast; ring
  rw [e3]
  have e4 : (((1 + u : ℝ)) : ℂ) ^ (-(p + q)) = (((1 + u : ℝ)) : ℂ) ^ (-(2 : ℂ)) *
      ((((1 + u : ℝ)) : ℂ) ^ (-(p - 1)) * (((1 + u : ℝ)) : ℂ) ^ (-(q - 1))) := by
    rw [← Complex.cpow_add _ _ h1c, ← Complex.cpow_add _ _ h1c]
    congr 1; ring
  rw [e4]
  ring

theorem measurable_ofReal_cpow (w : ℂ) : Measurable fun v : ℝ => (v : ℂ) ^ w :=
  Complex.measurable_ofReal.pow_const w

/-- `v ↦ v^{w−1}e^{−rv}` is integrable on `(0, ∞)` for `Re w > 0` and `r > 0`. -/
theorem integrableOn_cpow_mul_exp {w : ℂ} (hw : 0 < w.re) {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun v : ℝ => (v : ℂ) ^ (w - 1) * Complex.exp (-(r * v))) (Ioi 0) := by
  have hb := integrableOn_rpow_mul_exp_neg_mul_rpow (s := w.re - 1) (p := 1) (b := r)
    (by linarith) one_pos hr
  refine hb.mono' ?_ ?_
  · exact ((measurable_ofReal_cpow (w - 1)).mul (by fun_prop)).aestronglyMeasurable
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun v hv => ?_)
    have hv' : (0 : ℝ) < v := hv
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hv', Complex.norm_exp, Real.rpow_one]
    simp

/-- `∫_0^∞ t^{a−1}(1 + t²)^{−w} dt = ½B(a/2, w − a/2)`, by `u = t²`. -/
theorem integral_one_add_sq (a w : ℂ) :
    ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (a - 1) * (((1 + t ^ 2 : ℝ)) : ℂ) ^ (-w) =
      (1 / 2 : ℂ) * betaIntegral (a / 2) (w - a / 2) := by
  have h := mellin_comp_rpow (fun u : ℝ => (((1 + u : ℝ)) : ℂ) ^ (-w)) a (2 : ℝ)
  unfold mellin at h
  have e1 : ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (a - 1) * (((1 + t ^ 2 : ℝ)) : ℂ) ^ (-w) =
      ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (a - 1) • (((1 + t ^ (2 : ℝ) : ℝ)) : ℂ) ^ (-w) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    simp only [smul_eq_mul]
    rw [show t ^ (2 : ℝ) = t ^ 2 by norm_cast]
  rw [e1, h, abs_of_pos (by norm_num : (0 : ℝ) < 2), Complex.real_smul, ← integral_beta2]
  congr 1
  · push_cast; ring
  · refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
    simp only [smul_eq_mul]
    push_cast
    congr 2
    ring

/-- The reciprocal of `r_t = (t + 1/t)/2` is `2t/(1 + t²)`. -/
theorem inv_half_add_inv {t : ℝ} (ht : 0 < t) : 1 / ((t + t⁻¹) / 2) = 2 * t / (1 + t ^ 2) := by
  field_simp
  ring

/-- `∫_0^∞ v^{w−1}e^{−v(t + 1/t)/2} dv` in closed form. -/
theorem integral_bkK {w : ℂ} (hw : 0 < w.re) {t : ℝ} (ht : 0 < t) :
    ∫ v in Ioi (0 : ℝ), (v : ℂ) ^ (w - 1) * (bkK v t : ℂ) =
      (2 : ℂ) ^ w * (t : ℂ) ^ w * (((1 + t ^ 2 : ℝ)) : ℂ) ^ (-w) * Gamma w := by
  have hr : (0 : ℝ) < (t + t⁻¹) / 2 := by positivity
  have h := Complex.integral_cpow_mul_exp_neg_mul_Ioi hw hr
  have e1 : ∫ v in Ioi (0 : ℝ), (v : ℂ) ^ (w - 1) * (bkK v t : ℂ) =
      ∫ v in Ioi (0 : ℝ), (v : ℂ) ^ (w - 1) * Complex.exp (-(((t + t⁻¹) / 2 : ℝ) * v)) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
    unfold bkK
    rw [Complex.ofReal_exp]
    congr 2
    push_cast; ring
  rw [e1, h, ← Complex.ofReal_one, ← Complex.ofReal_div, inv_half_add_inv ht]
  have h1 : (0 : ℝ) < 1 + t ^ 2 := by positivity
  rw [div_eq_mul_inv, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (by positivity) (inv_nonneg.2 h1.le),
    Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (by norm_num) ht.le, Complex.ofReal_inv,
    Complex.inv_cpow _ _ (by rw [Complex.arg_ofReal_of_nonneg h1.le]; exact Real.pi_pos.ne),
    ← Complex.cpow_neg]
  push_cast
  ring

/-- The real majorant `t^{a−1}(2t/(1 + t²))^b` is integrable on `(0, ∞)` when `|a| < b`. -/
theorem integrableOn_bk_majorant {a b : ℝ} (hab : |a| < b) :
    IntegrableOn (fun t : ℝ => t ^ (a - 1) * (2 * t / (1 + t ^ 2)) ^ b) (Ioi 0) := by
  have hb : 0 < b := lt_of_le_of_lt (abs_nonneg a) hab
  have ha1 : -b < a := by have := neg_abs_le a; linarith
  have ha2 : a < b := lt_of_le_of_lt (le_abs_self a) hab
  have hmeas : AEStronglyMeasurable (fun t : ℝ => t ^ (a - 1) * (2 * t / (1 + t ^ 2)) ^ b)
      (volume.restrict (Ioi 0)) := (by fun_prop : Measurable fun t : ℝ =>
        t ^ (a - 1) * (2 * t / (1 + t ^ 2)) ^ b).aestronglyMeasurable
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
  refine IntegrableOn.union ?_ ?_
  · have h0 : IntegrableOn (fun t : ℝ => t ^ (a + b - 1)) (Ioc 0 1) := by
      rw [integrableOn_Ioc_iff_integrableOn_Ioo]
      exact (intervalIntegral.integrableOn_Ioo_rpow_iff one_pos).2 (by linarith)
    have hint : IntegrableOn (fun t : ℝ => 2 ^ b * t ^ (a + b - 1)) (Ioc 0 1) :=
      Integrable.const_mul h0 _
    refine hint.mono' (hmeas.mono_set Ioc_subset_Ioi_self) ?_
    refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun t ht => ?_)
    have ht0 : 0 < t := ht.1
    have h1 : 0 ≤ 2 * t / (1 + t ^ 2) := by positivity
    have h2 : 2 * t / (1 + t ^ 2) ≤ 2 * t := by
      rw [div_le_iff₀ (by positivity)]; nlinarith [sq_nonneg t]
    rw [Real.norm_of_nonneg (by positivity)]
    calc t ^ (a - 1) * (2 * t / (1 + t ^ 2)) ^ b ≤ t ^ (a - 1) * (2 * t) ^ b :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow h1 h2 hb.le) (by positivity)
      _ = 2 ^ b * t ^ (a + b - 1) := by
          rw [Real.mul_rpow (by norm_num) ht0.le, show a + b - 1 = (a - 1) + b by ring,
            Real.rpow_add ht0]
          ring
  · have hint : IntegrableOn (fun t : ℝ => 2 ^ b * t ^ (a - b - 1)) (Ioi 1) :=
      Integrable.const_mul ((integrableOn_Ioi_rpow_iff one_pos).2 (by linarith)) _
    refine hint.mono' (hmeas.mono_set (Ioi_subset_Ioi zero_le_one)) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_)
    have ht1 : (1 : ℝ) < t := ht
    have ht0 : 0 < t := by linarith
    have h1 : 0 ≤ 2 * t / (1 + t ^ 2) := by positivity
    have h2 : 2 * t / (1 + t ^ 2) ≤ 2 * t⁻¹ := by
      rw [div_le_iff₀ (by positivity)]
      field_simp
      nlinarith [sq_nonneg t]
    rw [Real.norm_of_nonneg (by positivity)]
    calc t ^ (a - 1) * (2 * t / (1 + t ^ 2)) ^ b ≤ t ^ (a - 1) * (2 * t⁻¹) ^ b :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow h1 h2 hb.le) (by positivity)
      _ = 2 ^ b * t ^ (a - b - 1) := by
          rw [Real.mul_rpow (by norm_num) (by positivity), Real.inv_rpow ht0.le,
            show a - b - 1 = (a - 1) + -b by ring, Real.rpow_add ht0, Real.rpow_neg ht0.le]
          ring

/-- **The Mellin transform of `K_ν`** (the companion paper's (A.15) in general form): for
`|Re ν| < Re w`, `∫_0^∞ v^{w−1}K_ν(v) dv = 2^{w−2}Γ((w−ν)/2)Γ((w+ν)/2)`. -/
theorem mellin_besselK {ν w : ℂ} (hν : |ν.re| < w.re) :
    mellin (fun v => besselK ν v) w = 2 ^ (w - 2) * Gamma ((w - ν) / 2) * Gamma ((w + ν) / 2) := by
  have hw : 0 < w.re := lt_of_le_of_lt (abs_nonneg _) hν
  have hp : 0 < ((ν + w) / 2).re := by
    have := neg_abs_le ν.re
    rw [Complex.div_ofNat_re, Complex.add_re]
    linarith
  have hq : 0 < (w - (ν + w) / 2).re := by
    have := le_abs_self ν.re
    rw [Complex.sub_re, Complex.div_ofNat_re, Complex.add_re]
    linarith
  set F : ℝ → ℝ → ℂ := fun v t => (v : ℂ) ^ (w - 1) * ((t : ℂ) ^ (ν - 1) * (bkK v t : ℂ)) with hF
  have hmeas : AEStronglyMeasurable (Function.uncurry F)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
    refine Measurable.aestronglyMeasurable ?_
    have h1 : Measurable fun p : ℝ × ℝ => (p.1 : ℂ) ^ (w - 1) :=
      (measurable_ofReal_cpow (w - 1)).comp measurable_fst
    have h2 : Measurable fun p : ℝ × ℝ => (p.2 : ℂ) ^ (ν - 1) :=
      (measurable_ofReal_cpow (ν - 1)).comp measurable_snd
    have h3 : Measurable fun p : ℝ × ℝ => (bkK p.1 p.2 : ℂ) := by
      unfold bkK; fun_prop
    exact h1.mul (h2.mul h3)
  have hint : Integrable (Function.uncurry F)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
    rw [integrable_prod_iff' hmeas]
    constructor
    · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_)
      have ht0 : (0 : ℝ) < t := ht
      have hr : (0 : ℝ) < (t + t⁻¹) / 2 := by positivity
      have hI : IntegrableOn (fun v : ℝ => (t : ℂ) ^ (ν - 1) * ((v : ℂ) ^ (w - 1) *
          Complex.exp (-(((t + t⁻¹) / 2 : ℝ) * v)))) (Ioi 0) :=
        Integrable.const_mul (integrableOn_cpow_mul_exp hw hr) _
      refine IntegrableOn.congr_fun hI (fun v _ => ?_) measurableSet_Ioi
      simp only [Function.uncurry_apply_pair, hF]
      unfold bkK
      rw [Complex.ofReal_exp]
      push_cast
      ring_nf
    · have hmaj : IntegrableOn (fun t : ℝ => Real.Gamma w.re *
          (t ^ (ν.re - 1) * (2 * t / (1 + t ^ 2)) ^ w.re)) (Ioi 0) :=
        Integrable.const_mul (integrableOn_bk_majorant hν) _
      refine IntegrableOn.congr_fun hmaj (fun t ht => ?_) measurableSet_Ioi
      have ht0 : (0 : ℝ) < t := ht
      have hr : (0 : ℝ) < (t + t⁻¹) / 2 := by positivity
      simp only [Function.uncurry_apply_pair, hF]
      have e : ∀ v ∈ Ioi (0 : ℝ), ‖(v : ℂ) ^ (w - 1) * ((t : ℂ) ^ (ν - 1) * (bkK v t : ℂ))‖ =
          t ^ (ν.re - 1) * (v ^ (w.re - 1) * Real.exp (-((t + t⁻¹) / 2 * v))) := by
        intro v hv
        have hv0 : (0 : ℝ) < v := hv
        rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hv0,
          Complex.norm_cpow_eq_rpow_re_of_pos ht0, Complex.norm_real, Real.norm_of_nonneg (bkK_pos v t).le]
        unfold bkK
        simp only [Complex.sub_re, Complex.one_re]
        rw [show -(v / 2) * (t + t⁻¹) = -((t + t⁻¹) / 2 * v) by ring]
        ring
      rw [setIntegral_congr_fun measurableSet_Ioi e, integral_const_mul,
        integral_rpow_mul_exp_neg_mul_Ioi hw hr, inv_half_add_inv ht0]
      ring
  -- the computation
  have hsw := integral_integral_swap hint
  show ∫ v in Ioi (0 : ℝ), (v : ℂ) ^ (w - 1) • besselK ν v = _
  have hK : ∀ v, besselK ν v = (1 / 2 : ℂ) * ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (ν - 1) • (bkK v t : ℂ) :=
    fun v => rfl
  have e1 : ∫ v in Ioi (0 : ℝ), (v : ℂ) ^ (w - 1) • besselK ν v =
      (1 / 2 : ℂ) * ∫ v in Ioi (0 : ℝ), ∫ t in Ioi (0 : ℝ), F v t := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
    rw [hK v, smul_eq_mul]
    calc (v : ℂ) ^ (w - 1) * ((1 / 2 : ℂ) * ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (ν - 1) • (bkK v t : ℂ))
        = (1 / 2 : ℂ) * ((v : ℂ) ^ (w - 1) * ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (ν - 1) • (bkK v t : ℂ)) := by
          ring
      _ = (1 / 2 : ℂ) * ∫ t in Ioi (0 : ℝ), F v t := by
          rw [← integral_const_mul]
          simp only [smul_eq_mul, hF]
  rw [e1, hsw]
  have e2 : ∫ t in Ioi (0 : ℝ), ∫ v in Ioi (0 : ℝ), F v t =
      (2 : ℂ) ^ w * Gamma w * ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ ((ν + w) - 1) * (((1 + t ^ 2 : ℝ)) : ℂ) ^ (-w) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht0 : (0 : ℝ) < t := ht
    have htc : (t : ℂ) ≠ 0 := by exact_mod_cast ht0.ne'
    have e3 : ∫ v in Ioi (0 : ℝ), F v t =
        (t : ℂ) ^ (ν - 1) * ∫ v in Ioi (0 : ℝ), (v : ℂ) ^ (w - 1) * (bkK v t : ℂ) := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun v => ?_)
      simp only [hF]
      ring
    rw [e3, integral_bkK hw ht0, show (ν + w) - 1 = (ν - 1) + w by ring, Complex.cpow_add _ _ htc]
    ring
  rw [e2, integral_one_add_sq, Complex.betaIntegral_eq_Gamma_mul_div _ _ hp hq,
    show (ν + w) / 2 + (w - (ν + w) / 2) = w by ring, show w - (ν + w) / 2 = (w - ν) / 2 by ring,
    show (ν + w) / 2 = (w + ν) / 2 by ring, Complex.cpow_sub _ _ two_ne_zero]
  have hG : Gamma w ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hw
  field_simp
  norm_num
  ring

/-- **The Bessel–Mellin integral of the theta series** (the companion paper's (A.15)): for `a > 0`
and `Re s > −1/3`, `∫_0^∞ v^{2s}K_{1/3}(av) dv = 2^{2s−1}Γ(s + 1/3)Γ(s + 2/3)a^{−(2s+1)}`. -/
theorem integral_besselK_third {s : ℂ} (hs : -1 / 3 < s.re) {a : ℝ} (ha : 0 < a) :
    ∫ v in Ioi (0 : ℝ), (v : ℂ) ^ (2 * s) * besselK (1 / 3) (a * v) =
      2 ^ (2 * s - 1) * Gamma (s + 1 / 3) * Gamma (s + 2 / 3) * (a : ℂ) ^ (-(2 * s + 1)) := by
  have hν : |((1 / 3 : ℂ)).re| < (2 * s + 1).re := by
    have e1 : ((1 / 3 : ℂ)).re = 1 / 3 := by norm_num
    have e2 : (2 * s + 1).re = 2 * s.re + 1 := by simp
    rw [e1, e2, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 3)]
    linarith
  have h := mellin_comp_mul_left (fun v => besselK (1 / 3) v) (2 * s + 1) ha
  rw [mellin_besselK hν] at h
  unfold mellin at h
  have e : ∫ v in Ioi (0 : ℝ), (v : ℂ) ^ (2 * s) * besselK (1 / 3) (a * v) =
      ∫ v in Ioi (0 : ℝ), (v : ℂ) ^ (2 * s + 1 - 1) • besselK (1 / 3) (a * v) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
    rw [smul_eq_mul, add_sub_cancel_right]
  rw [e, h, smul_eq_mul, show (2 * s + 1 - 1 / 3) / 2 = s + 1 / 3 by ring,
    show (2 * s + 1 + 1 / 3) / 2 = s + 2 / 3 by ring, show 2 * s + 1 - 2 = 2 * s - 1 by ring]
  ring

end Eis

end

#print axioms Eis.image_div_one_add
#print axioms Eis.cpow_ofReal_div_one_add
#print axioms Eis.integral_beta2
#print axioms Eis.measurable_ofReal_cpow
#print axioms Eis.integrableOn_cpow_mul_exp
#print axioms Eis.integral_one_add_sq
#print axioms Eis.inv_half_add_inv
#print axioms Eis.integral_bkK
#print axioms Eis.integrableOn_bk_majorant
#print axioms Eis.mellin_besselK
#print axioms Eis.integral_besselK_third
