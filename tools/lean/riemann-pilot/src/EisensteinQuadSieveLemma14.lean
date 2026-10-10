import EisensteinQuadSieveSep

/-! # The quadratic large sieve, part 4a: the planar Lemma 14 (round 347)

S5e of round 312's plan, the first piece of round 343's S5e-4: Heath-Brown's Lemma 14 in the plane,
for the majorant `Φ` of round 301, whose transform is `𝓕Φ(w) = G(|w|)` (`dualG`).

* **The kernels** (`integral_kernel_eq`, `integral_dual_kernel_eq`): for `w, x ≠ 0`,
  `∫_0^∞ t^{−1/2}e^{−πt|w|²} dt = |w|⁻¹` and `∫_0^∞ t^{−3/2}e^{−π|x|²/t} dt = |x|⁻¹`, from
  `Γ(1/2) = √π` and the substitution `t ↦ 1/t`.
* **The Gaussian on `ℂ`** (`fourier_gaussian_plane`): `𝓕(e^{−πt|w|²})(x) = t⁻¹e^{−π|x|²/t}`, and
  Parseval against it (`integral_fourier_mul_gaussian`), from the self-adjointness of `𝓕`.
* **`|x|⁻¹` is self-dual on `ℂ`** (`integral_fourier_mul_inv_norm`): `∫ 𝓕F(w)|w|⁻¹ dw =
  ∫ F(x)|x|⁻¹ dx` for every Schwartz `F`. Both sides are superpositions of Gaussians in `t`, and
  Fubini applies on each side (`integrable_norm_mul_inv_norm`).
* **Polar coordinates** (`integral_radial_mul_inv_norm`, `integral_radial_sq`):
  `∫ h(|w|)|w|⁻¹ dw = 2π∫_0^∞ h` and `∫ h(κ|z|²) dz = (π/κ)∫_0^∞ h` for `κ > 0`.
* **On the ray** (`integral_dualG_Ioi`): `∫_0^∞ G = ∫_0^∞ Φ`, the self-duality for the radial `Φ`.
* **The planar Lemma 14** (`integral_fourier_Phi_sq`): `∫_ℂ 𝓕Φ(αz²) dz = |α|⁻¹∫_ℂ Φ(z²) dz` for
  `α ≠ 0`. Heath-Brown's factor `1 − sign(α)i` has no counterpart: `Φ` and `𝓕Φ` are radial. The
  form used for the main terms is `integral_dualG_sq`, `∫_ℂ G(a|z|²) dz = (π/a)∫_0^∞ Φ` for
  `a > 0`, with `integral_radial_sq` for `∫_ℂ Φ(b|z|²) dz`.
-/

open Complex MeasureTheory Set
open scoped FourierTransform SchwartzMap

noncomputable section

namespace Eis

/-- `∫_0^∞ t^{−1/2}e^{−at} dt = √π/√a` for `a > 0`. -/
theorem integral_rpow_neg_half_exp {a : ℝ} (ha : 0 < a) :
    ∫ t in Ioi (0 : ℝ), t ^ (-(1 / 2 : ℝ)) * Real.exp (-(a * t)) = Real.sqrt Real.pi / Real.sqrt a := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 1 / 2) (r := a) (by norm_num) ha
  rw [show (1 / 2 : ℝ) - 1 = -(1 / 2) by norm_num, Real.Gamma_one_half_eq] at h
  rw [h, ← Real.sqrt_eq_rpow, Real.sqrt_div' 1 ha.le, Real.sqrt_one]
  field_simp

theorem integrableOn_rpow_neg_half_exp {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun t : ℝ => t ^ (-(1 / 2 : ℝ)) * Real.exp (-(a * t))) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := -(1 / 2)) (b := a)
    (by norm_num) one_pos ha
  refine h.congr_fun (fun t _ => ?_) measurableSet_Ioi
  simp only [Real.rpow_one, neg_mul]

/-- **The kernel**: `∫_0^∞ t^{−1/2}e^{−πt|w|²} dt = |w|⁻¹` for `w ≠ 0`. -/
theorem integral_kernel_eq {w : ℂ} (hw : w ≠ 0) :
    ∫ t in Ioi (0 : ℝ), t ^ (-(1 / 2 : ℝ)) * Real.exp (-(Real.pi * ‖w‖ ^ 2 * t)) = ‖w‖⁻¹ := by
  have hw' : 0 < ‖w‖ := norm_pos_iff.2 hw
  rw [integral_rpow_neg_half_exp (by positivity), Real.sqrt_mul Real.pi_pos.le,
    Real.sqrt_sq hw'.le]
  have : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
  field_simp

/-- `∫_0^∞ t^{−3/2}e^{−a/t} dt = √π/√a` for `a > 0`, by `t ↦ 1/t`. -/
theorem integral_rpow_neg_three_half_exp {a : ℝ} (ha : 0 < a) :
    ∫ t in Ioi (0 : ℝ), t ^ (-(3 / 2 : ℝ)) * Real.exp (-(a / t)) = Real.sqrt Real.pi / Real.sqrt a := by
  have h := integral_comp_rpow_Ioi (fun y : ℝ => y ^ (-(1 / 2 : ℝ)) * Real.exp (-(a * y)))
    (p := -1) (by norm_num)
  rw [integral_rpow_neg_half_exp ha] at h
  rw [← h]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht' : 0 < t := ht
  simp only [smul_eq_mul]
  rw [show (|(-1 : ℝ)|) = 1 by norm_num, one_mul, ← Real.rpow_mul ht'.le, Real.rpow_neg_one]
  rw [show (-1 : ℝ) - 1 = -2 by norm_num, show (-1 : ℝ) * -(1 / 2) = 1 / 2 by norm_num]
  rw [← mul_assoc, ← Real.rpow_add ht', show (-2 : ℝ) + 1 / 2 = -(3 / 2) by norm_num,
    div_eq_mul_inv a t]

theorem integrableOn_rpow_neg_three_half_exp {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun t : ℝ => t ^ (-(3 / 2 : ℝ)) * Real.exp (-(a / t))) (Ioi 0) := by
  have h := (integrableOn_Ioi_comp_rpow_iff
    (fun y : ℝ => y ^ (-(1 / 2 : ℝ)) * Real.exp (-(a * y))) (p := -1) (by norm_num)).2
    (integrableOn_rpow_neg_half_exp ha)
  refine h.congr_fun (fun t ht => ?_) measurableSet_Ioi
  have ht' : 0 < t := ht
  simp only [smul_eq_mul]
  rw [show (|(-1 : ℝ)|) = 1 by norm_num, one_mul, ← Real.rpow_mul ht'.le, Real.rpow_neg_one]
  rw [show (-1 : ℝ) - 1 = -2 by norm_num, show (-1 : ℝ) * -(1 / 2) = 1 / 2 by norm_num]
  rw [← mul_assoc, ← Real.rpow_add ht', show (-2 : ℝ) + 1 / 2 = -(3 / 2) by norm_num,
    div_eq_mul_inv a t]

/-- **The dual kernel**: `∫_0^∞ t^{−3/2}e^{−π|x|²/t} dt = |x|⁻¹` for `x ≠ 0`. -/
theorem integral_dual_kernel_eq {x : ℂ} (hx : x ≠ 0) :
    ∫ t in Ioi (0 : ℝ), t ^ (-(3 / 2 : ℝ)) * Real.exp (-(Real.pi * ‖x‖ ^ 2 / t)) = ‖x‖⁻¹ := by
  have hx' : 0 < ‖x‖ := norm_pos_iff.2 hx
  rw [integral_rpow_neg_three_half_exp (by positivity), Real.sqrt_mul Real.pi_pos.le,
    Real.sqrt_sq hx'.le]
  have : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
  field_simp

/-- **The Gaussian on `ℂ`**: `𝓕(e^{−πt|w|²})(x) = t⁻¹e^{−π|x|²/t}`. -/
theorem fourier_gaussian_plane {t : ℝ} (ht : 0 < t) (x : ℂ) :
    𝓕 (fun w : ℂ => cexp (-((Real.pi * t : ℝ) : ℂ) * (‖w‖ : ℂ) ^ 2)) x =
      ((t⁻¹ : ℝ) : ℂ) * cexp (-((Real.pi / t : ℝ) : ℂ) * (‖x‖ : ℂ) ^ 2) := by
  have hb : 0 < (((Real.pi * t : ℝ)) : ℂ).re := by
    rw [Complex.ofReal_re]; positivity
  rw [fourier_gaussian_innerProductSpace hb x, Complex.finrank_real_complex]
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
  have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  congr 1
  · rw [show ((2 : ℕ) : ℂ) / 2 = 1 by norm_num, Complex.cpow_one]
    push_cast
    field_simp
  · congr 1
    push_cast
    field_simp

theorem integrable_gaussian_plane {t : ℝ} (ht : 0 < t) :
    Integrable (fun w : ℂ => cexp (-((Real.pi * t : ℝ) : ℂ) * (‖w‖ : ℂ) ^ 2)) := by
  have hb : 0 < (((Real.pi * t : ℝ)) : ℂ).re := by
    rw [Complex.ofReal_re]; positivity
  have := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := ℂ) hb 0 0
  simpa using this

/-- **Parseval against a Gaussian**: `∫ 𝓕F(w)e^{−πt|w|²} dw = ∫ F(x)·t⁻¹e^{−π|x|²/t} dx`. -/
theorem integral_fourier_mul_gaussian (F : 𝓢(ℂ, ℂ)) {t : ℝ} (ht : 0 < t) :
    ∫ w : ℂ, 𝓕 (F : ℂ → ℂ) w * cexp (-((Real.pi * t : ℝ) : ℂ) * (‖w‖ : ℂ) ^ 2) =
      ∫ x : ℂ, F x * (((t⁻¹ : ℝ) : ℂ) * cexp (-((Real.pi / t : ℝ) : ℂ) * (‖x‖ : ℂ) ^ 2)) := by
  have key := VectorFourier.integral_fourierIntegral_smul_eq_flip (e := Real.fourierChar)
    (μ := (volume : Measure ℂ)) (ν := volume) (L := innerₗ ℂ) Real.continuous_fourierChar
    continuous_inner F.integrable (integrable_gaussian_plane ht)
  simp only [smul_eq_mul, flip_innerₗ] at key
  have e1 : ∀ f : ℂ → ℂ, VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ ℂ) f =
      𝓕 f := fun f => rfl
  rw [e1, e1] at key
  rw [key]
  congr 1
  funext x
  rw [fourier_gaussian_plane ht x]

/-- `w ↦ |w|⁻¹(1 + |w|)⁻³` is integrable on `ℂ`, in polar coordinates. -/
theorem integrable_inv_norm_mul_one_add_pow :
    Integrable (fun w : ℂ => ‖w‖⁻¹ * ((1 + ‖w‖) ^ 3)⁻¹) := by
  refine (integrable_fun_norm_addHaar (μ := (volume : Measure ℂ))
    (f := fun y : ℝ => y⁻¹ * ((1 + y) ^ 3)⁻¹)).2 ?_
  have hR : Integrable (fun y : ℝ => (1 + ‖y‖) ^ (-(3 : ℝ))) :=
    integrable_one_add_norm (by rw [Module.finrank_self]; norm_num)
  refine hR.integrableOn.congr_fun (fun y hy => ?_) measurableSet_Ioi
  have hy' : 0 < y := hy
  simp only [Complex.finrank_real_complex, smul_eq_mul, Real.norm_eq_abs, abs_of_pos hy']
  rw [show 2 - 1 = 1 by norm_num, pow_one, ← mul_assoc, mul_inv_cancel₀ hy'.ne', one_mul,
    Real.rpow_neg (by positivity), show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

/-- **`|F(w)|/|w|` is integrable** for a Schwartz function `F` on `ℂ`. -/
theorem integrable_norm_mul_inv_norm (F : 𝓢(ℂ, ℂ)) :
    Integrable (fun w : ℂ => ‖F w‖ * ‖w‖⁻¹) := by
  set C : ℝ := 2 ^ 3 * (Finset.Iic ((3 : ℕ), (0 : ℕ))).sup
    (fun m => SchwartzMap.seminorm ℝ m.1 m.2) F with hC
  have hbound : ∀ w : ℂ, (1 + ‖w‖) ^ 3 * ‖F w‖ ≤ C := by
    intro w
    have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := ((3 : ℕ), (0 : ℕ)))
      (k := 3) (n := 0) le_rfl le_rfl F w
    rwa [norm_iteratedFDeriv_zero] at h
  refine (integrable_inv_norm_mul_one_add_pow.const_mul C).mono' ?_ ?_
  · exact (F.continuous.norm.aestronglyMeasurable).mul
      (continuous_norm.measurable.inv.aestronglyMeasurable)
  · refine Filter.Eventually.of_forall fun w => ?_
    have h1 : 0 < (1 + ‖w‖) ^ 3 := by positivity
    rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (inv_nonneg.2 (norm_nonneg _)))]
    have h2 : ‖F w‖ ≤ C * ((1 + ‖w‖) ^ 3)⁻¹ := by
      rw [le_mul_inv_iff₀ h1, mul_comm]; exact hbound w
    calc ‖F w‖ * ‖w‖⁻¹ ≤ C * ((1 + ‖w‖) ^ 3)⁻¹ * ‖w‖⁻¹ :=
          mul_le_mul_of_nonneg_right h2 (inv_nonneg.2 (norm_nonneg _))
      _ = C * (‖w‖⁻¹ * ((1 + ‖w‖) ^ 3)⁻¹) := by ring

theorem ae_ne_zero_complex : ∀ᵐ w : ℂ, w ≠ 0 := by
  refine ae_iff.2 ?_
  simp

/-- The pointwise form of the kernel against a Gaussian. -/
theorem kernel_cast (w : ℂ) (t : ℝ) :
    (((t ^ (-(1 / 2 : ℝ)) * Real.exp (-(Real.pi * ‖w‖ ^ 2 * t)) : ℝ)) : ℂ) =
      ((t ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * cexp (-((Real.pi * t : ℝ) : ℂ) * (‖w‖ : ℂ) ^ 2) := by
  rw [Complex.ofReal_mul, Complex.ofReal_exp]
  congr 2
  push_cast; ring

theorem dual_kernel_cast {t : ℝ} (ht : 0 < t) (x : ℂ) :
    ((t ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * (((t⁻¹ : ℝ) : ℂ) *
      cexp (-((Real.pi / t : ℝ) : ℂ) * (‖x‖ : ℂ) ^ 2)) =
      (((t ^ (-(3 / 2 : ℝ)) * Real.exp (-(Real.pi * ‖x‖ ^ 2 / t)) : ℝ)) : ℂ) := by
  have h : t ^ (-(1 / 2 : ℝ)) * t⁻¹ = t ^ (-(3 / 2 : ℝ)) := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add ht]; norm_num
  rw [← mul_assoc, ← Complex.ofReal_mul, h, Complex.ofReal_mul, Complex.ofReal_exp]
  congr 2
  push_cast; ring

/-- **`1/|x|` is self-dual on `ℂ`**: `∫ 𝓕F(w)·|w|⁻¹ dw = ∫ F(x)·|x|⁻¹ dx` for Schwartz `F`. -/
theorem integral_fourier_mul_inv_norm (F : 𝓢(ℂ, ℂ)) :
    ∫ w : ℂ, 𝓕 (F : ℂ → ℂ) w * ((‖w‖⁻¹ : ℝ) : ℂ) = ∫ x : ℂ, F x * ((‖x‖⁻¹ : ℝ) : ℂ) := by
  set G : 𝓢(ℂ, ℂ) := 𝓕 F with hGd
  have hG : ∀ w, 𝓕 (F : ℂ → ℂ) w = G w := fun w => by rw [hGd, SchwartzMap.fourier_coe]
  set k : ℂ → ℝ → ℝ := fun w t => t ^ (-(1 / 2 : ℝ)) * Real.exp (-(Real.pi * ‖w‖ ^ 2 * t))
    with hk
  set k' : ℂ → ℝ → ℝ := fun x t => t ^ (-(3 / 2 : ℝ)) * Real.exp (-(Real.pi * ‖x‖ ^ 2 / t))
    with hk'
  have hk0 : ∀ w, ∀ t ∈ Ioi (0 : ℝ), 0 ≤ k w t := fun w t ht =>
    mul_nonneg (Real.rpow_nonneg (le_of_lt ht) _) (Real.exp_pos _).le
  have hk'0 : ∀ x, ∀ t ∈ Ioi (0 : ℝ), 0 ≤ k' x t := fun x t ht =>
    mul_nonneg (Real.rpow_nonneg (le_of_lt ht) _) (Real.exp_pos _).le
  -- the integrals of the kernels
  have hkint : ∀ w : ℂ, w ≠ 0 → IntegrableOn (k w) (Ioi 0) := fun w hw =>
    integrableOn_rpow_neg_half_exp (a := Real.pi * ‖w‖ ^ 2) (by
      have := norm_pos_iff.2 hw; positivity)
  have hk'int : ∀ x : ℂ, x ≠ 0 → IntegrableOn (k' x) (Ioi 0) := fun x hx =>
    integrableOn_rpow_neg_three_half_exp (a := Real.pi * ‖x‖ ^ 2) (by
      have := norm_pos_iff.2 hx; positivity)
  -- integrability on the product
  have hint1 : Integrable (Function.uncurry fun (w : ℂ) (t : ℝ) => G w * ((k w t : ℝ) : ℂ))
      ((volume : Measure ℂ).prod (volume.restrict (Ioi (0 : ℝ)))) := by
    have hmeas : AEStronglyMeasurable (Function.uncurry fun (w : ℂ) (t : ℝ) =>
        G w * ((k w t : ℝ) : ℂ)) ((volume : Measure ℂ).prod (volume.restrict (Ioi (0 : ℝ)))) := by
      refine Measurable.aestronglyMeasurable ?_
      have h1 : Measurable fun p : ℂ × ℝ => G p.1 := G.continuous.measurable.comp measurable_fst
      have h2 : Measurable fun p : ℂ × ℝ => k p.1 p.2 := by
        simp only [hk]
        refine Measurable.mul ?_ ?_
        · exact measurable_snd.pow_const _
        · exact Real.measurable_exp.comp (by fun_prop)
      exact h1.mul (Complex.measurable_ofReal.comp h2)
    rw [integrable_prod_iff hmeas]
    refine ⟨?_, ?_⟩
    · filter_upwards [ae_ne_zero_complex] with w hw
      exact ((hkint w hw).ofReal).const_mul (G w)
    · refine (integrable_norm_mul_inv_norm G).congr ?_
      filter_upwards [ae_ne_zero_complex] with w hw
      simp only [Function.uncurry_apply_pair, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      rw [integral_const_mul, setIntegral_congr_fun measurableSet_Ioi
        (fun t ht => abs_of_nonneg (hk0 w t ht)), integral_kernel_eq hw]
  have hint2 : Integrable (Function.uncurry fun (x : ℂ) (t : ℝ) => F x * ((k' x t : ℝ) : ℂ))
      ((volume : Measure ℂ).prod (volume.restrict (Ioi (0 : ℝ)))) := by
    have hmeas : AEStronglyMeasurable (Function.uncurry fun (x : ℂ) (t : ℝ) =>
        F x * ((k' x t : ℝ) : ℂ)) ((volume : Measure ℂ).prod (volume.restrict (Ioi (0 : ℝ)))) := by
      refine Measurable.aestronglyMeasurable ?_
      have h1 : Measurable fun p : ℂ × ℝ => F p.1 := F.continuous.measurable.comp measurable_fst
      have h2 : Measurable fun p : ℂ × ℝ => k' p.1 p.2 := by
        simp only [hk']
        refine Measurable.mul ?_ ?_
        · exact measurable_snd.pow_const _
        · exact Real.measurable_exp.comp (by fun_prop)
      exact h1.mul (Complex.measurable_ofReal.comp h2)
    rw [integrable_prod_iff hmeas]
    refine ⟨?_, ?_⟩
    · filter_upwards [ae_ne_zero_complex] with x hx
      exact ((hk'int x hx).ofReal).const_mul (F x)
    · refine (integrable_norm_mul_inv_norm F).congr ?_
      filter_upwards [ae_ne_zero_complex] with x hx
      simp only [Function.uncurry_apply_pair, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      rw [integral_const_mul, setIntegral_congr_fun measurableSet_Ioi
        (fun t ht => abs_of_nonneg (hk'0 x t ht)), integral_dual_kernel_eq hx]
  calc ∫ w : ℂ, 𝓕 (F : ℂ → ℂ) w * ((‖w‖⁻¹ : ℝ) : ℂ)
      = ∫ w : ℂ, ∫ t in Ioi (0 : ℝ), G w * ((k w t : ℝ) : ℂ) := by
        refine integral_congr_ae ?_
        filter_upwards [ae_ne_zero_complex] with w hw
        rw [integral_const_mul, integral_complex_ofReal, hG, integral_kernel_eq hw]
    _ = ∫ t in Ioi (0 : ℝ), ∫ w : ℂ, G w * ((k w t : ℝ) : ℂ) := integral_integral_swap hint1
    _ = ∫ t in Ioi (0 : ℝ), ∫ x : ℂ, F x * ((k' x t : ℝ) : ℂ) := by
        refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
        have ht' : 0 < t := ht
        calc ∫ w : ℂ, G w * ((k w t : ℝ) : ℂ)
            = ((t ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * ∫ w : ℂ, 𝓕 (F : ℂ → ℂ) w *
                cexp (-((Real.pi * t : ℝ) : ℂ) * (‖w‖ : ℂ) ^ 2) := by
              rw [← integral_const_mul]
              refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
              simp only [hk]
              rw [kernel_cast, hG]; ring
          _ = ((t ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * ∫ x : ℂ, F x * (((t⁻¹ : ℝ) : ℂ) *
                cexp (-((Real.pi / t : ℝ) : ℂ) * (‖x‖ : ℂ) ^ 2)) := by
              rw [integral_fourier_mul_gaussian F ht']
          _ = ∫ x : ℂ, F x * ((k' x t : ℝ) : ℂ) := by
              rw [← integral_const_mul]
              refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
              simp only [hk']
              rw [← dual_kernel_cast ht' x]; ring
    _ = ∫ x : ℂ, ∫ t in Ioi (0 : ℝ), F x * ((k' x t : ℝ) : ℂ) :=
        (integral_integral_swap hint2).symm
    _ = ∫ x : ℂ, F x * ((‖x‖⁻¹ : ℝ) : ℂ) := by
        refine integral_congr_ae ?_
        filter_upwards [ae_ne_zero_complex] with x hx
        rw [integral_const_mul, integral_complex_ofReal, integral_dual_kernel_eq hx]

/-- **`Φ` is radial**: `Φ(w) = Φ(|w|)`. -/
theorem Phi_eq_norm (w : ℂ) : Majorant.Phi w = Majorant.Phi ((‖w‖ : ℝ) : ℂ) := by
  have hw : w = ((Circle.exp (Complex.arg w) : Circle) : ℂ) * ((‖w‖ : ℝ) : ℂ) := by
    rw [Circle.coe_exp, mul_comm]; exact (norm_mul_exp_arg_mul_I w).symm
  conv_lhs => rw [hw]
  exact Majorant.Phi_rot _ _

/-- **Polar coordinates with the weight `|w|⁻¹`**: `∫ h(|w|)|w|⁻¹ dw = 2π∫_0^∞ h`. -/
theorem integral_radial_mul_inv_norm (h : ℝ → ℂ) :
    ∫ w : ℂ, h ‖w‖ * ((‖w‖⁻¹ : ℝ) : ℂ) = 2 * Real.pi * ∫ y in Ioi (0 : ℝ), h y := by
  have hp := integral_fun_norm_addHaar (μ := (volume : Measure ℂ))
    (f := fun y : ℝ => h y * ((y⁻¹ : ℝ) : ℂ))
  rw [hp, Complex.finrank_real_complex, Measure.real, Complex.volume_ball]
  have hI : ∫ y in Ioi (0 : ℝ), y ^ (2 - 1) • (h y * ((y⁻¹ : ℝ) : ℂ)) =
      ∫ y in Ioi (0 : ℝ), h y := by
    refine setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
    have hy' : (y : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hy)
    simp only [show 2 - 1 = 1 by norm_num, pow_one, Complex.real_smul]
    push_cast
    field_simp
  rw [hI]
  simp only [ENNReal.ofReal_one, one_pow, one_mul, ENNReal.coe_toReal, NNReal.coe_real_pi,
    nsmul_eq_mul, Complex.real_smul]
  push_cast
  ring

/-- **The scaled radial integral**: `∫ h(κ|z|²) dz = (π/κ)∫_0^∞ h` for `κ > 0`. -/
theorem integral_radial_sq {κ : ℝ} (hκ : 0 < κ) (h : ℝ → ℂ) :
    ∫ z : ℂ, h (κ * ‖z‖ ^ 2) = ((Real.pi / κ : ℝ) : ℂ) * ∫ s in Ioi (0 : ℝ), h s := by
  have hp := integral_fun_norm_addHaar (μ := (volume : Measure ℂ))
    (f := fun y : ℝ => h (κ * y ^ 2))
  rw [hp, Complex.finrank_real_complex, Measure.real, Complex.volume_ball]
  have hsub := integral_comp_rpow_Ioi_of_pos (g := fun s : ℝ => h (κ * s)) (p := 2) two_pos
  have hscale := integral_comp_mul_left_Ioi h 0 hκ
  rw [mul_zero] at hscale
  have hI : ∫ y in Ioi (0 : ℝ), y ^ (2 - 1) • h (κ * y ^ 2) =
      ((2⁻¹ : ℝ) : ℂ) * ∫ s in Ioi (0 : ℝ), h (κ * s) := by
    rw [← hsub, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun y _ => ?_
    simp only [show 2 - 1 = 1 by norm_num, pow_one, Complex.real_smul, Real.rpow_two,
      show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one]
    push_cast
    ring
  rw [hI, hscale]
  simp only [ENNReal.ofReal_one, one_pow, one_mul, ENNReal.coe_toReal, NNReal.coe_real_pi,
    nsmul_eq_mul, Complex.real_smul]
  push_cast
  field_simp

/-- **The planar Lemma 14 on the ray**: `∫_0^∞ G = ∫_0^∞ Φ`, from the self-duality of `|x|⁻¹`
and the radial symmetry of `Φ` and `𝓕Φ`. -/
theorem integral_dualG_Ioi :
    ∫ s in Ioi (0 : ℝ), dualG s = ∫ s in Ioi (0 : ℝ), Majorant.Phi ((s : ℝ) : ℂ) := by
  have e1 := integral_radial_mul_inv_norm dualG
  have e2 := integral_radial_mul_inv_norm (fun s : ℝ => Majorant.Phi ((s : ℝ) : ℂ))
  have e3 := integral_fourier_mul_inv_norm Majorant.Phi
  have e3' : ∫ w : ℂ, dualG ‖w‖ * ((‖w‖⁻¹ : ℝ) : ℂ) =
      ∫ w : ℂ, 𝓕 (Majorant.Phi : ℂ → ℂ) w * ((‖w‖⁻¹ : ℝ) : ℂ) :=
    integral_congr_ae (Filter.Eventually.of_forall fun w => by
      dsimp only; rw [fourier_Phi_eq_dualG])
  have e4 : ∫ x : ℂ, Majorant.Phi x * ((‖x‖⁻¹ : ℝ) : ℂ) =
      ∫ x : ℂ, Majorant.Phi ((‖x‖ : ℝ) : ℂ) * ((‖x‖⁻¹ : ℝ) : ℂ) :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => by
      dsimp only; rw [← Phi_eq_norm])
  have h5 : (2 * Real.pi : ℂ) * ∫ y in Ioi (0 : ℝ), dualG y =
      (2 * Real.pi : ℂ) * ∫ y in Ioi (0 : ℝ), Majorant.Phi ((y : ℝ) : ℂ) := by
    rw [← e1, e3', e3, e4, e2]
  have h2pi : (2 * Real.pi : ℂ) ≠ 0 := by
    have : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
    exact mul_ne_zero two_ne_zero this
  exact mul_left_cancel₀ h2pi h5

/-- **The planar Lemma 14** (Heath-Brown's Lemma 14 in the plane, for the majorant):
`∫_ℂ 𝓕Φ(αz²) dz = |α|⁻¹∫_ℂ Φ(z²) dz` for `α ≠ 0`. -/
theorem integral_fourier_Phi_sq {α : ℂ} (hα : α ≠ 0) :
    ∫ z : ℂ, 𝓕 (Majorant.Phi : ℂ → ℂ) (α * z ^ 2) =
      ((‖α‖⁻¹ : ℝ) : ℂ) * ∫ z : ℂ, Majorant.Phi (z ^ 2) := by
  have hα' : 0 < ‖α‖ := norm_pos_iff.2 hα
  have hL : ∫ z : ℂ, 𝓕 (Majorant.Phi : ℂ → ℂ) (α * z ^ 2) =
      ∫ z : ℂ, dualG (‖α‖ * ‖z‖ ^ 2) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only
    rw [fourier_Phi_eq_dualG, norm_mul, norm_pow]
  have hR : ∫ z : ℂ, Majorant.Phi (z ^ 2) =
      ∫ z : ℂ, (fun s : ℝ => Majorant.Phi ((s : ℝ) : ℂ)) (1 * ‖z‖ ^ 2) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only
    rw [Phi_eq_norm, norm_pow, one_mul]
  have hP := integral_radial_sq one_pos (fun s : ℝ => Majorant.Phi ((s : ℝ) : ℂ))
  rw [hL, hR, integral_radial_sq hα' dualG, hP, integral_dualG_Ioi]
  push_cast
  field_simp


/-- **The main-term integral**: `∫_ℂ G(a|z|²) dz = (π/a)∫_0^∞ Φ` for `a > 0`. -/
theorem integral_dualG_sq {a : ℝ} (ha : 0 < a) :
    ∫ z : ℂ, dualG (a * ‖z‖ ^ 2) =
      ((Real.pi / a : ℝ) : ℂ) * ∫ s in Ioi (0 : ℝ), Majorant.Phi ((s : ℝ) : ℂ) := by
  rw [integral_radial_sq ha dualG, integral_dualG_Ioi]

end Eis

end

#print axioms Eis.integral_kernel_eq
#print axioms Eis.integral_dual_kernel_eq
#print axioms Eis.fourier_gaussian_plane
#print axioms Eis.integral_fourier_mul_gaussian
#print axioms Eis.integrable_norm_mul_inv_norm
#print axioms Eis.integral_fourier_mul_inv_norm
#print axioms Eis.integral_radial_mul_inv_norm
#print axioms Eis.integral_radial_sq
#print axioms Eis.integral_dualG_Ioi
#print axioms Eis.integral_fourier_Phi_sq
#print axioms Eis.integral_dualG_sq
