import KubotaThetaInv

/-! # The mean on `ℂ/3ℤ[ω]` under `z ↦ μz + t` (round 444)

S5f-12 of round 360's plan, part 5. Round 443's next step planned the cube eigenrelation through round 439's
`translates_eq_zero` on a cover of level `p³`, with the constant terms at `∞` of its traces computed from θ at
`∞`. In those traces θ is composed with upper triangular matrices, `z ↦ μz + t` on the horizontal coordinate.
This round proves that the mean over `3P` of a function periodic under `3ℤ[ω]` is unchanged by `z ↦ μz + t`
for `μ ∈ ℤ[ω]` nonzero, so that each such term is θ's constant term:

* **Change of variables** (**`lintegral_comp_mul_complex`**, with `det_mulLeft_complex`):
  `∫⁻ F(wz) dz = |w|⁻²∫⁻ F` for `w ≠ 0` (Mathlib's `map_linearMap_addHaar_eq_smul_addHaar` and
  `Algebra.norm_complex_apply`).
* **Tiling `μ·3P`** (**`tsum_fundP3_div`** and **`lintegral_indicator_div_fundP3`**): for `μ ∈ ℤ[ω]` nonzero,
  `Σ_{t∈ℤ[ω]} 1_{3P}((y + 3σ(t))/σ(μ)) = N(μ)` at every `y` (round 389's `tsum_fundP3` on each class modulo
  `μ`, through round 294's `repQ_bijective`), so `∫_{μ·3P} G = N(μ)·∫_{3P} G` for `G ≥ 0` measurable and
  periodic under `3ℤ[ω]` (round 389's `lintegral_tile3`).
* **The mean under `z ↦ μz + t`** (**`lintegral_fundP3_mul`**, **`integral_fundP3_mul`** and
  **`integral_fundP3_affine`**, with `integrableOn_fundP3_mul` and `integral_fundP3_mul_real`):
  `∫_{3P} f(μz + t) dz = ∫_{3P} f(z) dz` for `f` measurable, periodic under `3ℤ[ω]` and integrable on `3P`,
  `μ ∈ ℤ[ω]` nonzero and `t ∈ ℂ` (with round 443's `integral_fundP3_add`).
* **θ's constant term** (**`integral_thS_affine`**, with `integrableOn_thS_slice`):
  `∫_{3P} thS(μz + t, v) dz = (9√3/2)·Res φ·v^{2/3}` for `v > 0` (round 436's `integral_thS`).
-/

open MeasureTheory Set Filter NumberField Complex Ideal
open scoped ENNReal Topology

noncomputable section

namespace Eis

/-! ### Multiplication by a complex number -/

/-- Multiplication by `w`, as an `ℝ`-linear map of `ℂ`, has determinant `|w|²`. -/
theorem det_mulLeft_complex (w : ℂ) : LinearMap.det (LinearMap.mulLeft ℝ w) = Complex.normSq w := by
  rw [← Algebra.norm_complex_apply, Algebra.norm_apply]
  rfl

/-- **Change of variables**: `∫⁻ F(wz) dz = |w|⁻²∫⁻ F` for `w ≠ 0`. -/
theorem lintegral_comp_mul_complex {w : ℂ} (hw : w ≠ 0) {F : ℂ → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ z, F (w * z) = ENNReal.ofReal (Complex.normSq w)⁻¹ * ∫⁻ z, F z := by
  have hdet : LinearMap.det (LinearMap.mulLeft ℝ w) ≠ 0 := by
    rw [det_mulLeft_complex]
    exact (Complex.normSq_pos.2 hw).ne'
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar (μ := (volume : Measure ℂ)) hdet
  have hcont : Continuous (LinearMap.mulLeft ℝ w) := LinearMap.continuous_of_finiteDimensional _
  have e : ∫⁻ z, F (w * z) = ∫⁻ z, F (LinearMap.mulLeft ℝ w z) := rfl
  rw [e, ← lintegral_map hF hcont.measurable, hmap, lintegral_smul_measure, smul_eq_mul,
    det_mulLeft_complex, abs_inv, abs_of_nonneg (Complex.normSq_nonneg w)]

/-! ### Counting the translates in `μ·3P` -/

/-- **`μ·3P` holds `N(μ)` points of each class modulo `3ℤ[ω]`**:
`Σ_{t∈ℤ[ω]} 1_{3P}((y + 3σ(t))/σ(μ)) = N(μ)` for `μ ≠ 0`. -/
theorem tsum_fundP3_div {μ : 𝓞 K} (hμ : μ ≠ 0) (y : ℂ) :
    ∑' t : 𝓞 K, fundP3.indicator (1 : ℂ → ℝ≥0∞) ((y + σO (3 * t)) / σO μ) = absNorm (span {μ}) := by
  classical
  have := finite_quot μ hμ
  have := Fintype.ofFinite (𝓞 K ⧸ span {μ})
  have hσ : σO μ ≠ 0 := σO_ne_zero hμ
  rw [← (Equiv.ofBijective _ (repQ_bijective μ hμ)).tsum_eq]
  simp only [Equiv.ofBijective_apply]
  rw [ENNReal.tsum_prod (f := fun (q : 𝓞 K ⧸ span {μ}) (u : 𝓞 K) =>
    fundP3.indicator (1 : ℂ → ℝ≥0∞) ((y + σO (3 * (repQ μ q + μ * u))) / σO μ))]
  have key : ∀ q : 𝓞 K ⧸ span {μ}, ∑' u : 𝓞 K,
      fundP3.indicator (1 : ℂ → ℝ≥0∞) ((y + σO (3 * (repQ μ q + μ * u))) / σO μ) = 1 := by
    intro q
    rw [← tsum_fundP3 ((y + σO (3 * repQ μ q)) / σO μ)]
    refine tsum_congr fun u => ?_
    congr 1
    rw [σO_three_mul, σO_three_mul, σO_three_mul, map_add, map_mul]
    field_simp
    ring
  rw [tsum_congr key, tsum_fintype, Finset.sum_const, Finset.card_univ, card_quot, nsmul_eq_mul,
    mul_one]

/-- **Tiling `μ·3P` by `3P`**: `∫_{μ·3P} G = N(μ)·∫_{3P} G` for `G ≥ 0` measurable and periodic under
`3ℤ[ω]`. -/
theorem lintegral_indicator_div_fundP3 {G : ℂ → ℝ≥0∞} (hG : Measurable G)
    (hper : ∀ z u, G (z + σO (3 * u)) = G z) {μ : 𝓞 K} (hμ : μ ≠ 0) :
    ∫⁻ z, fundP3.indicator (1 : ℂ → ℝ≥0∞) (z / σO μ) * G z =
      absNorm (span {μ}) * ∫⁻ z in fundP3, G z := by
  have hi : Measurable fun z : ℂ => fundP3.indicator (1 : ℂ → ℝ≥0∞) (z / σO μ) :=
    (measurable_one.indicator measurableSet_fundP3).comp (measurable_id.div_const _)
  rw [lintegral_tile3 (G := fun z => fundP3.indicator (1 : ℂ → ℝ≥0∞) (z / σO μ) * G z) (hi.mul hG)]
  simp only [hper]
  rw [← lintegral_tsum (f := fun (t : 𝓞 K) (y : ℂ) =>
    fundP3.indicator (1 : ℂ → ℝ≥0∞) ((y + σO (3 * t)) / σO μ) * G y)
    fun t => ((hi.comp (measurable_add_const _)).mul hG).aemeasurable]
  simp_rw [ENNReal.tsum_mul_right, tsum_fundP3_div hμ]
  exact lintegral_const_mul _ hG

/-! ### The mean on `ℂ/3ℤ[ω]` under multiplication by `μ` -/

/-- **The mean is invariant under multiplication by `μ`**: `∫_{3P} G(μz) dz = ∫_{3P} G` for `G ≥ 0` measurable
and periodic under `3ℤ[ω]`, and `μ ∈ ℤ[ω]` nonzero. -/
theorem lintegral_fundP3_mul {G : ℂ → ℝ≥0∞} (hG : Measurable G)
    (hper : ∀ z u, G (z + σO (3 * u)) = G z) {μ : 𝓞 K} (hμ : μ ≠ 0) :
    ∫⁻ z in fundP3, G (σO μ * z) = ∫⁻ z in fundP3, G z := by
  have hσ : σO μ ≠ 0 := σO_ne_zero hμ
  have hi : Measurable fun z : ℂ => fundP3.indicator (1 : ℂ → ℝ≥0∞) (z / σO μ) :=
    (measurable_one.indicator measurableSet_fundP3).comp (measurable_id.div_const _)
  have e1 : ∫⁻ z in fundP3, G (σO μ * z) =
      ∫⁻ z, fundP3.indicator (1 : ℂ → ℝ≥0∞) (σO μ * z / σO μ) * G (σO μ * z) := by
    rw [← lintegral_indicator measurableSet_fundP3]
    refine lintegral_congr fun z => ?_
    rw [mul_div_cancel_left₀ _ hσ]
    by_cases hz : z ∈ fundP3
    · simp [hz]
    · simp [hz]
  rw [e1, lintegral_comp_mul_complex hσ (F := fun w => fundP3.indicator (1 : ℂ → ℝ≥0∞) (w / σO μ) * G w)
    (hi.mul hG), lintegral_indicator_div_fundP3 hG hper hμ, normSq_σO, ← mul_assoc]
  have hN : (absNorm (span {μ}) : ℝ≥0∞) ≠ 0 := by
    have : absNorm (span {μ}) ≠ 0 := by
      rw [Ne, absNorm_eq_zero_iff, span_singleton_eq_bot]
      exact hμ
    exact_mod_cast this
  rw [ENNReal.ofReal_inv_of_pos (by exact_mod_cast Nat.pos_of_ne_zero (by exact_mod_cast hN)),
    ENNReal.ofReal_natCast, ENNReal.inv_mul_cancel hN (ENNReal.natCast_ne_top _), one_mul]

/-- The `μ`-scaled function is integrable on `3P` with the function. -/
theorem integrableOn_fundP3_mul {f : ℂ → ℂ} (hf : Measurable f) (hper : ∀ z u, f (z + σO (3 * u)) = f z)
    {μ : 𝓞 K} (hμ : μ ≠ 0) (hint : IntegrableOn f fundP3) :
    IntegrableOn (fun z => f (σO μ * z)) fundP3 := by
  refine ⟨(hf.comp (measurable_const_mul _)).aestronglyMeasurable, ?_⟩
  show ∫⁻ z in fundP3, ‖f (σO μ * z)‖ₑ < ⊤
  rw [lintegral_fundP3_mul (G := fun z => ‖f z‖ₑ) hf.enorm (fun z u => by rw [hper]) hμ]
  exact hint.2

/-- `integral_fundP3_mul` for real `f`, through the positive and negative parts. -/
theorem integral_fundP3_mul_real {f : ℂ → ℝ} (hf : Measurable f) (hper : ∀ z u, f (z + σO (3 * u)) = f z)
    {μ : 𝓞 K} (hμ : μ ≠ 0) (hint : IntegrableOn f fundP3) :
    ∫ z in fundP3, f (σO μ * z) = ∫ z in fundP3, f z := by
  have hint' : IntegrableOn (fun z => f (σO μ * z)) fundP3 := by
    refine ⟨(hf.comp (measurable_const_mul _)).aestronglyMeasurable, ?_⟩
    show ∫⁻ z in fundP3, ‖f (σO μ * z)‖ₑ < ⊤
    rw [lintegral_fundP3_mul (G := fun z => ‖f z‖ₑ) hf.enorm (fun z u => by rw [hper]) hμ]
    exact hint.2
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hint',
    integral_eq_lintegral_pos_part_sub_lintegral_neg_part hint,
    lintegral_fundP3_mul (G := fun z => ENNReal.ofReal (f z)) (ENNReal.measurable_ofReal.comp hf)
      (fun z u => by rw [hper]) hμ,
    lintegral_fundP3_mul (G := fun z => ENNReal.ofReal (-f z)) (ENNReal.measurable_ofReal.comp hf.neg)
      (fun z u => by simp only [hper]) hμ]

/-- **The mean on `ℂ/3ℤ[ω]` is invariant under multiplication by `μ`**: `∫_{3P} f(μz) dz = ∫_{3P} f` for `f`
measurable, periodic under `3ℤ[ω]` and integrable on `3P`, and `μ ∈ ℤ[ω]` nonzero. -/
theorem integral_fundP3_mul {f : ℂ → ℂ} (hf : Measurable f) (hper : ∀ z u, f (z + σO (3 * u)) = f z)
    {μ : 𝓞 K} (hμ : μ ≠ 0) (hint : IntegrableOn f fundP3) :
    ∫ z in fundP3, f (σO μ * z) = ∫ z in fundP3, f z := by
  have hint' := integrableOn_fundP3_mul hf hper hμ hint
  apply Complex.ext
  · have e1 := integral_re hint'
    have e2 := integral_re hint
    simp only [RCLike.re_to_complex] at e1 e2
    rw [← e1, ← e2]
    exact integral_fundP3_mul_real (Complex.measurable_re.comp hf)
      (fun z u => by simp only [Function.comp_apply, hper]) hμ
      hint.re
  · have e1 := integral_im hint'
    have e2 := integral_im hint
    simp only [RCLike.im_to_complex] at e1 e2
    rw [← e1, ← e2]
    exact integral_fundP3_mul_real (Complex.measurable_im.comp hf)
      (fun z u => by simp only [Function.comp_apply, hper]) hμ
      hint.im

/-- **The mean on `ℂ/3ℤ[ω]` is invariant under `z ↦ μz + t`**, for `μ ∈ ℤ[ω]` nonzero and `t ∈ ℂ`. -/
theorem integral_fundP3_affine {f : ℂ → ℂ} (hf : Measurable f) (hper : ∀ z u, f (z + σO (3 * u)) = f z)
    {μ : 𝓞 K} (hμ : μ ≠ 0) (hint : IntegrableOn f fundP3) (t : ℂ) :
    ∫ z in fundP3, f (σO μ * z + t) = ∫ z in fundP3, f z := by
  have hσ : σO μ ≠ 0 := σO_ne_zero hμ
  have h1 := integral_fundP3_add (f := fun z => f (σO μ * z)) (fun z u => by
      show f (σO μ * (z + σO (3 * u))) = f (σO μ * z)
      rw [mul_add, show σO μ * σO (3 * u) = σO (3 * (μ * u)) by
        rw [σO_three_mul, σO_three_mul, map_mul]; ring, hper]) (t / σO μ)
  have e : (fun z => f (σO μ * (z + t / σO μ))) = fun z => f (σO μ * z + t) :=
    funext fun z => by rw [mul_add, mul_div_cancel₀ _ hσ]
  simp only [e] at h1
  rw [h1, integral_fundP3_mul hf hper hμ hint]

/-! ### θ's constant term from the affine images of `3P` -/

/-- θ's series is integrable on `3P` at every height (round 437's `continuous_thS_slice`). -/
theorem integrableOn_thS_slice {r : ℝ} (hr : 0 < r) {Y : ℝ} (hY : 0 < Y) {v : ℝ} (hv : 0 < v) :
    IntegrableOn (fun z => thS r Y hY (z, v)) fundP3 :=
  ((continuous_thS_slice hr hY hv).continuousOn.integrableOn_compact
    (isCompact_closedBall (0 : ℂ) 6)).mono_set
    fun _ hz => mem_closedBall_zero_iff.2 (norm_le_six_of_mem_fundP3 hz)

/-- **θ's constant term from an affine image of `3P`**: `∫_{3P} thS(μz + t, v) dz = (9√3/2)·Res φ·v^{2/3}` for
`v > 0`, `μ ∈ ℤ[ω]` nonzero and `t ∈ ℂ` (round 436's `integral_thS`). -/
theorem integral_thS_affine {r : ℝ} (hr : 0 < r) {Y : ℝ} (hY : 0 < Y) {v : ℝ} (hv : 0 < v) {μ : 𝓞 K}
    (hμ : μ ≠ 0) (t : ℂ) :
    ∫ z in fundP3, thS r Y hY (σO μ * z + t, v) =
      ((9 * (Real.sqrt 3 / 2) : ℝ) : ℂ) * (phiG (4 / 3) / 3) * ((v ^ (2 / 3 : ℝ) : ℝ) : ℂ) := by
  rw [integral_fundP3_affine (f := fun z => thS r Y hY (z, v)) (continuous_thS_slice hr hY hv).measurable
    (fun z u => thS_add_period r Y hY z u v) hμ (integrableOn_thS_slice hr hY hv) t, integral_thS hr hY hv]

end Eis

end

#print axioms Eis.det_mulLeft_complex
#print axioms Eis.lintegral_comp_mul_complex
#print axioms Eis.tsum_fundP3_div
#print axioms Eis.lintegral_indicator_div_fundP3
#print axioms Eis.lintegral_fundP3_mul
#print axioms Eis.integrableOn_fundP3_mul
#print axioms Eis.integral_fundP3_mul_real
#print axioms Eis.integral_fundP3_mul
#print axioms Eis.integral_fundP3_affine
#print axioms Eis.integrableOn_thS_slice
#print axioms Eis.integral_thS_affine
