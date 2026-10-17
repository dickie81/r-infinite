import UpperHalfSpace

/-! # The invariant measure on upper half-space (round 383)

S5f-8 of round 360's plan, part 1. Upper half-space is `{(z, v) ∈ ℂ × ℝ : v > 0}` (`UHS`), with round
361's action `uhsAct` of `SL_2(ℂ)`. This file proves that the measure `dz dv/v³` is invariant under every
`g` of determinant `1`.

* **The change of variables** (`lintegral_UHS_comp`, `UInv`, `uinv_of_jac`): Mathlib's
  `lintegral_image_eq_lintegral_abs_det_fderiv_mul` on `{v > 0}`. A map `f`, injective on `{v > 0}`
  with image `{v > 0}`, and with `|det f′(p)|·v(f(p))⁻³ = v⁻³`, preserves `v⁻³ dz dv`. The property
  `UInv f` is closed under composition (`UInv.comp`) and depends only on `f` on `{v > 0}` (`UInv.congr`).
* **The inversion** (`e3` and `psiInv`, definitions; `uinv_psiInv`): `ψ(p) = p/(|z|² + v²)`, transported
  from Mathlib's inversion of `ℝ³`. Its derivative is Mathlib's `hasFDerivAt_inversion`, `(1/‖x‖)²`
  times a reflection, of determinant `−‖x‖⁻⁶` by Mathlib's `Submodule.det_reflection`
  (`det_inversion_deriv`, `det_psiInv`).
* **The building blocks**: `τ(z, v) = (−z̄, v)` (`uinv_tauR`, determinant `−1`), the translations
  (`uinv_transl`), and `(a, 0; 0, a⁻¹)`, which acts by `(z, v) ↦ (a²z, |a|²v)` (`uhsAct_diag`,
  `uinv_diag`, determinant `|a|⁶`). The inversion `E = (0, −1; 1, 0)` acts on `{v > 0}` by `τ ∘ ψ`
  (`uinv_actP_E`, from round 361's `uhsAct_inv`).
* **Every `g` of determinant `1`** (**`uinv_actP`**): `g = (1, a/c; 0, 1)·E·(c, 0; 0, c⁻¹)·(1, d/c; 0, 1)`
  for `c ≠ 0`, and `g = (a, 0; 0, a⁻¹)·(1, b/a; 0, 1)` for `c = 0`, with round 361's `uhsAct_mul`.
* **The measure** (`uhsMeasure`, a definition; **`measurePreserving_actP`**, with `lintegral_actP` and
  `integral_actP`): `dz dv/v³` on `{v > 0}`, preserved by `actP g` for `det g = 1`.
-/

open MeasureTheory Set Module
open scoped ENNReal ComplexConjugate

noncomputable section

namespace Eis

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The determinant of the derivative of the inversion `x ↦ x/‖x‖²` of `ℝ³`: `−‖x‖⁻⁶`. -/
theorem det_inversion_deriv {x : E3} (hx : x ≠ 0) :
    LinearMap.det (((1 / dist x 0) ^ 2 • ((ℝ ∙ (x - 0))ᗮ.reflection : E3 →L[ℝ] E3)) : E3 →ₗ[ℝ] E3) =
      -(‖x‖ ^ 2)⁻¹ ^ 3 := by
  have hx' : x - 0 ≠ 0 := by simpa using hx
  have hK : finrank ℝ ((ℝ ∙ (x - 0))ᗮᗮ) = 1 := by
    rw [Submodule.orthogonal_orthogonal]; exact finrank_span_singleton hx'
  rw [LinearMap.det_smul, finrank_euclideanSpace_fin]
  have hr : LinearMap.det (((ℝ ∙ (x - 0))ᗮ.reflection : E3 →L[ℝ] E3) : E3 →ₗ[ℝ] E3) = -1 := by
    have := Submodule.det_reflection (ℝ ∙ (x - 0))ᗮ
    rw [hK, pow_one] at this
    exact this
  rw [hr, dist_zero_right]
  field_simp

/-- `ℂ × ℝ ≅ ℝ³`, `(z, v) ↦ (Re z, Im z, v)`. -/
def e3L : (ℂ × ℝ) ≃ₗ[ℝ] E3 where
  toFun p := WithLp.toLp 2 ![p.1.re, p.1.im, p.2]
  invFun x := (⟨x 0, x 1⟩, x 2)
  map_add' p q := by ext i; fin_cases i <;> simp
  map_smul' c p := by ext i; fin_cases i <;> simp
  left_inv p := by simp
  right_inv x := by ext i; fin_cases i <;> simp

/-- `ℂ × ℝ ≅ ℝ³` as a continuous linear equivalence. -/
def e3 : (ℂ × ℝ) ≃L[ℝ] E3 := e3L.toContinuousLinearEquiv

theorem e3_apply (p : ℂ × ℝ) : e3 p = WithLp.toLp 2 ![p.1.re, p.1.im, p.2] := rfl

theorem norm_e3_sq (p : ℂ × ℝ) : ‖e3 p‖ ^ 2 = Complex.normSq p.1 + p.2 ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, e3_apply, Fin.sum_univ_three, Complex.normSq_apply]
  simp; ring

/-- `volume` on `ℂ × ℝ` is the product of Haar measures, hence a Haar measure. -/
instance isAddHaarMeasure_volume_CR : (volume : Measure (ℂ × ℝ)).IsAddHaarMeasure :=
  (inferInstance : ((volume : Measure ℂ).prod (volume : Measure ℝ)).IsAddHaarMeasure)

/-- Upper half-space `{v > 0}` in `ℂ × ℝ`. -/
def UHS : Set (ℂ × ℝ) := {p | 0 < p.2}

theorem measurableSet_UHS : MeasurableSet UHS := measurableSet_lt measurable_const measurable_snd

/-- **The change of variables on upper half-space**: for `f` injective on `{v > 0}` with image
`{v > 0}`, and `|det f′(p)|·v(f(p))⁻³ = v⁻³`, the measure `v⁻³ dz dv` is invariant under `f`. -/
theorem lintegral_UHS_comp {f : ℂ × ℝ → ℂ × ℝ} {f' : ℂ × ℝ → (ℂ × ℝ →L[ℝ] ℂ × ℝ)}
    (hf' : ∀ p ∈ UHS, HasFDerivWithinAt f (f' p) UHS p) (hinj : InjOn f UHS) (himg : f '' UHS = UHS)
    (hJ : ∀ p ∈ UHS, |(f' p).det| * (f p).2 ^ (-3 : ℤ) = p.2 ^ (-3 : ℤ)) (F : ℂ × ℝ → ℝ≥0∞) :
    ∫⁻ p in UHS, F (f p) * ENNReal.ofReal (p.2 ^ (-3 : ℤ)) =
      ∫⁻ p in UHS, F p * ENNReal.ofReal (p.2 ^ (-3 : ℤ)) := by
  have h := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume measurableSet_UHS hf' hinj
    (fun p => F p * ENNReal.ofReal (p.2 ^ (-3 : ℤ)))
  rw [himg] at h
  rw [h]
  refine setLIntegral_congr_fun measurableSet_UHS (fun p hp => ?_)
  rw [← hJ p hp, ENNReal.ofReal_mul (abs_nonneg _)]
  ring

/-- The inversion `p ↦ p/(|z|² + v²)` of `ℂ × ℝ`, transported from Mathlib's inversion of `ℝ³`. -/
def psiInv (p : ℂ × ℝ) : ℂ × ℝ := e3.symm (EuclideanGeometry.inversion 0 1 (e3 p))

theorem psiInv_apply (p : ℂ × ℝ) : psiInv p = ((Complex.normSq p.1 + p.2 ^ 2)⁻¹ : ℝ) • p := by
  unfold psiInv EuclideanGeometry.inversion
  rw [dist_zero_right, vsub_eq_sub, sub_zero, vadd_eq_add, add_zero, map_smul,
    ContinuousLinearEquiv.symm_apply_apply, div_pow, one_pow, norm_e3_sq, one_div]

theorem e3_ne_zero {p : ℂ × ℝ} (hp : p ∈ UHS) : e3 p ≠ 0 := by
  intro h
  have := congrArg (fun x : E3 => x 2) h
  simp [e3_apply] at this
  exact (show (0 : ℝ) < p.2 from hp).ne' this

theorem hasFDerivAt_psiInv {p : ℂ × ℝ} (hp : p ∈ UHS) :
    HasFDerivAt psiInv ((e3.symm : E3 →L[ℝ] ℂ × ℝ).comp
      (((1 / dist (e3 p) 0) ^ 2 • ((ℝ ∙ (e3 p - 0))ᗮ.reflection : E3 →L[ℝ] E3)).comp
        (e3 : ℂ × ℝ →L[ℝ] E3))) p :=
  (e3.symm.hasFDerivAt).comp p
    ((EuclideanGeometry.hasFDerivAt_inversion (e3_ne_zero hp)).comp p e3.hasFDerivAt)

theorem det_psiInv {p : ℂ × ℝ} (hp : p ∈ UHS) :
    ((e3.symm : E3 →L[ℝ] ℂ × ℝ).comp
      (((1 / dist (e3 p) 0) ^ 2 • ((ℝ ∙ (e3 p - 0))ᗮ.reflection : E3 →L[ℝ] E3)).comp
        (e3 : ℂ × ℝ →L[ℝ] E3))).det = -((Complex.normSq p.1 + p.2 ^ 2)⁻¹) ^ 3 := by
  have h := LinearMap.det_conj
    (((1 / dist (e3 p) 0) ^ 2 • ((ℝ ∙ (e3 p - 0))ᗮ.reflection : E3 →L[ℝ] E3)) : E3 →ₗ[ℝ] E3)
    e3L.symm
  rw [det_inversion_deriv (e3_ne_zero hp), norm_e3_sq] at h
  rw [← h]
  rfl

/-- The density `v⁻³` of the invariant measure. -/
def uhsW (p : ℂ × ℝ) : ℝ≥0∞ := ENNReal.ofReal (p.2 ^ (-3 : ℤ))

/-- **`f` preserves `v⁻³ dz dv` on upper half-space**, tested against every `F ≥ 0`. -/
def UInv (f : ℂ × ℝ → ℂ × ℝ) : Prop :=
  ∀ F : ℂ × ℝ → ℝ≥0∞, ∫⁻ p in UHS, F (f p) * uhsW p = ∫⁻ p in UHS, F p * uhsW p

theorem UInv.comp {f g : ℂ × ℝ → ℂ × ℝ} (hf : UInv f) (hg : UInv g) : UInv (f ∘ g) := fun F => by
  have := hg (F ∘ f)
  simp only [Function.comp_apply] at this ⊢
  rw [this, hf F]

theorem UInv.congr {f g : ℂ × ℝ → ℂ × ℝ} (hf : UInv f) (h : ∀ p ∈ UHS, f p = g p) : UInv g := fun F => by
  rw [← hf F]
  exact setLIntegral_congr_fun measurableSet_UHS (fun p hp => by rw [h p hp])

theorem uinv_of_jac {f : ℂ × ℝ → ℂ × ℝ} {f' : ℂ × ℝ → (ℂ × ℝ →L[ℝ] ℂ × ℝ)}
    (hf' : ∀ p ∈ UHS, HasFDerivWithinAt f (f' p) UHS p) (hinj : InjOn f UHS) (himg : f '' UHS = UHS)
    (hJ : ∀ p ∈ UHS, |(f' p).det| * (f p).2 ^ (-3 : ℤ) = p.2 ^ (-3 : ℤ)) : UInv f :=
  fun F => lintegral_UHS_comp hf' hinj himg hJ F

/-- An involution of `ℂ × ℝ` preserving `{v > 0}` maps it onto itself, injectively. -/
theorem image_eq_of_invol {f : ℂ × ℝ → ℂ × ℝ} (hff : ∀ p, f (f p) = p) (hU : ∀ p ∈ UHS, f p ∈ UHS) :
    InjOn f UHS ∧ f '' UHS = UHS := by
  refine ⟨fun p _ q _ h => by rw [← hff p, h, hff q], ?_⟩
  ext q
  exact ⟨fun ⟨p, hp, hpq⟩ => hpq ▸ hU p hp, fun hq => ⟨f q, hU q hq, hff q⟩⟩

theorem psiInv_psiInv (p : ℂ × ℝ) : psiInv (psiInv p) = p := by
  unfold psiInv
  rw [ContinuousLinearEquiv.apply_symm_apply, EuclideanGeometry.inversion_inversion 0 one_ne_zero,
    ContinuousLinearEquiv.symm_apply_apply]

theorem rsq_pos {p : ℂ × ℝ} (hp : p ∈ UHS) : 0 < Complex.normSq p.1 + p.2 ^ 2 := by
  have : (0 : ℝ) < p.2 := hp
  have := Complex.normSq_nonneg p.1
  positivity

theorem psiInv_snd (p : ℂ × ℝ) : (psiInv p).2 = (Complex.normSq p.1 + p.2 ^ 2)⁻¹ * p.2 := by
  rw [psiInv_apply]; rfl

/-- **The inversion preserves the measure.** -/
theorem uinv_psiInv : UInv psiInv := by
  have hU : ∀ p ∈ UHS, psiInv p ∈ UHS := fun p hp => by
    show 0 < (psiInv p).2
    rw [psiInv_snd]; exact mul_pos (inv_pos.2 (rsq_pos hp)) hp
  obtain ⟨hinj, himg⟩ := image_eq_of_invol psiInv_psiInv hU
  refine uinv_of_jac (fun p hp => (hasFDerivAt_psiInv hp).hasFDerivWithinAt) hinj himg ?_
  intro p hp
  rw [det_psiInv hp, psiInv_snd, abs_neg]
  have hr := rsq_pos hp
  have hv : (0 : ℝ) < p.2 := hp
  rw [abs_of_pos (by positivity), mul_zpow, inv_zpow', neg_neg]
  field_simp

/-- `τ(z, v) = (−z̄, v)`. -/
def tauR (p : ℂ × ℝ) : ℂ × ℝ := (-conj p.1, p.2)

/-- `τ` as a continuous linear map. -/
def tauL : ℂ × ℝ →L[ℝ] ℂ × ℝ :=
  (-(Complex.conjCLE : ℂ →L[ℝ] ℂ)).prodMap (ContinuousLinearMap.id ℝ ℝ)

theorem tauL_apply (p : ℂ × ℝ) : tauL p = tauR p := rfl

theorem det_tauL : tauL.det = -1 := by
  unfold tauL
  rw [ContinuousLinearMap.det, ContinuousLinearMap.coe_prodMap, LinearMap.det_prodMap]
  simp only [ContinuousLinearMap.coe_id, LinearMap.det_id, mul_one, ContinuousLinearMap.toLinearMap_neg]
  have : ((Complex.conjCLE : ℂ →L[ℝ] ℂ) : ℂ →ₗ[ℝ] ℂ) = Complex.conjAe.toLinearEquiv.toLinearMap := rfl
  rw [← neg_one_smul ℝ ((Complex.conjCLE : ℂ →L[ℝ] ℂ) : ℂ →ₗ[ℝ] ℂ), LinearMap.det_smul,
    Complex.finrank_real_complex, this, Complex.det_conjAe]
  norm_num

theorem uinv_tauR : UInv tauR := by
  have hU : ∀ p ∈ UHS, tauR p ∈ UHS := fun p hp => hp
  obtain ⟨hinj, himg⟩ := image_eq_of_invol (fun p => by simp [tauR]) hU
  refine uinv_of_jac (f' := fun _ => tauL) (fun p _ => ?_) hinj himg (fun p _ => ?_)
  · have : tauR = tauL := funext tauL_apply |>.symm
    rw [this]; exact tauL.hasFDerivAt.hasFDerivWithinAt
  · rw [det_tauL]; simp [tauR]

/-- **Translations** `(z, v) ↦ (z + b, v)` preserve the measure. -/
theorem uinv_transl (b : ℂ) : UInv (fun p : ℂ × ℝ => (p.1 + b, p.2)) := by
  have hinj : InjOn (fun p : ℂ × ℝ => (p.1 + b, p.2)) UHS := fun p _ q _ h => by
    simp only [Prod.mk.injEq, add_left_inj] at h; exact Prod.ext h.1 h.2
  have himg : (fun p : ℂ × ℝ => (p.1 + b, p.2)) '' UHS = UHS := by
    ext q
    exact ⟨fun ⟨p, hp, hpq⟩ => hpq ▸ hp, fun hq => ⟨(q.1 - b, q.2), hq, by simp⟩⟩
  refine uinv_of_jac (f' := fun _ => ContinuousLinearMap.id ℝ (ℂ × ℝ)) (fun p _ => ?_) hinj himg
    (fun p _ => by simp [ContinuousLinearMap.det])
  have h : (fun p : ℂ × ℝ => (p.1 + b, p.2)) = fun p => p + (b, 0) := by
    funext p; ext <;> simp
  rw [h]; exact ((hasFDerivAt_id p).add_const _).hasFDerivWithinAt

/-- The action of `SL_2(ℂ)` on pairs `(z, v)`. -/
def actP (g : Matrix (Fin 2) (Fin 2) ℂ) (p : ℂ × ℝ) : ℂ × ℝ := uhsAct g p.1 p.2

theorem actP_mul {g h : Matrix (Fin 2) (Fin 2) ℂ} (hg : g.det = 1) (hh : h.det = 1) {p : ℂ × ℝ}
    (hp : p ∈ UHS) : actP (g * h) p = actP g (actP h p) := uhsAct_mul hg hh p.1 hp

theorem actP_mem {g : Matrix (Fin 2) (Fin 2) ℂ} (hg : g.det = 1) {p : ℂ × ℝ} (hp : p ∈ UHS) :
    actP g p ∈ UHS := uhsAct_pos hg p.1 hp

/-- The diagonal matrix `(a, 0; 0, a⁻¹)` acts by `(z, v) ↦ (a²z, |a|²v)`. -/
theorem uhsAct_diag {a : ℂ} (ha : a ≠ 0) (z : ℂ) (v : ℝ) :
    uhsAct !![a, 0; 0, a⁻¹] z v = (a ^ 2 * z, Complex.normSq a * v) := by
  have hn : Complex.normSq a ≠ 0 := (Complex.normSq_pos.2 ha).ne'
  have hc : conj a ≠ 0 := (map_ne_zero _).2 ha
  simp only [uhsAct, uhsZ, uhsV, uhsDen, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, zero_mul, zero_add, add_zero,
    mul_zero, map_zero, map_inv₀]
  refine Prod.ext ?_ ?_
  · simp only
    rw [Complex.ofReal_inv, Complex.normSq_eq_conj_mul_self]
    field_simp
  · simp only
    field_simp

/-- The diagonal action as a continuous linear map. -/
def diagL (a : ℂ) : ℂ × ℝ →L[ℝ] ℂ × ℝ :=
  (ContinuousLinearMap.restrictScalars ℝ ((a ^ 2) • ContinuousLinearMap.id ℂ ℂ)).prodMap
    (Complex.normSq a • ContinuousLinearMap.id ℝ ℝ)

theorem diagL_apply (a : ℂ) (p : ℂ × ℝ) : diagL a p = (a ^ 2 * p.1, Complex.normSq a * p.2) := rfl

theorem det_diagL (a : ℂ) : (diagL a).det = Complex.normSq a ^ 3 := by
  unfold diagL
  rw [ContinuousLinearMap.det, ContinuousLinearMap.coe_prodMap, LinearMap.det_prodMap]
  have h1 : ((ContinuousLinearMap.restrictScalars ℝ ((a ^ 2) • ContinuousLinearMap.id ℂ ℂ) :
      ℂ →L[ℝ] ℂ) : ℂ →ₗ[ℝ] ℂ) = (((a ^ 2) • LinearMap.id : ℂ →ₗ[ℂ] ℂ)).restrictScalars ℝ := rfl
  rw [h1, LinearMap.det_restrictScalars, LinearMap.det_smul, LinearMap.det_id, Module.finrank_self,
    pow_one, mul_one, Algebra.norm_complex_apply, map_pow]
  rw [ContinuousLinearMap.toLinearMap_smul, LinearMap.det_smul]
  simp only [ContinuousLinearMap.coe_id, LinearMap.det_id, Module.finrank_self, pow_one, mul_one]
  ring

theorem uinv_diag {a : ℂ} (ha : a ≠ 0) :
    UInv (fun p : ℂ × ℝ => (a ^ 2 * p.1, Complex.normSq a * p.2)) := by
  have hn : 0 < Complex.normSq a := Complex.normSq_pos.2 ha
  have ha2 : a ^ 2 ≠ 0 := pow_ne_zero 2 ha
  have hinj : InjOn (fun p : ℂ × ℝ => (a ^ 2 * p.1, Complex.normSq a * p.2)) UHS := fun p _ q _ h => by
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (mul_left_cancel₀ ha2 h.1) (mul_left_cancel₀ hn.ne' h.2)
  have himg : (fun p : ℂ × ℝ => (a ^ 2 * p.1, Complex.normSq a * p.2)) '' UHS = UHS := by
    ext q
    refine ⟨fun ⟨p, hp, hpq⟩ => hpq ▸ (mul_pos hn hp : 0 < Complex.normSq a * p.2), fun hq => ?_⟩
    refine ⟨(q.1 / a ^ 2, q.2 / Complex.normSq a), div_pos hq hn, ?_⟩
    ext
    · simp only; field_simp
    · simp only; field_simp
  refine uinv_of_jac (f' := fun _ => diagL a) (fun p _ => ?_) hinj himg (fun p hp => ?_)
  · have : (fun p : ℂ × ℝ => (a ^ 2 * p.1, Complex.normSq a * p.2)) = diagL a := funext fun p => rfl
    rw [this]; exact (diagL a).hasFDerivAt.hasFDerivWithinAt
  · have hv : (0 : ℝ) < p.2 := hp
    rw [det_diagL, abs_of_pos (by positivity), mul_zpow]
    field_simp

/-- **The inversion `E = (0, −1; 1, 0)` preserves the measure**: on `{v > 0}` it is `τ ∘ ψ`. -/
theorem uinv_actP_E : UInv (actP !![0, -1; 1, 0]) := by
  refine (uinv_tauR.comp uinv_psiInv).congr (fun p hp => ?_)
  simp only [Function.comp_apply, actP, uhsAct_inv, tauR, psiInv_apply, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul]
  refine Prod.ext ?_ ?_
  · simp only
    rw [Complex.real_smul, map_mul, Complex.conj_ofReal, div_eq_mul_inv, Complex.ofReal_inv]
    ring
  · simp only; rw [div_eq_mul_inv]; ring

theorem det_transl (x : ℂ) : (!![1, x; 0, 1] : Matrix (Fin 2) (Fin 2) ℂ).det = 1 := by
  simp [Matrix.det_fin_two_of]

theorem det_E : (!![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ).det = 1 := by
  simp [Matrix.det_fin_two_of]

theorem det_diag {a : ℂ} (ha : a ≠ 0) : (!![a, 0; 0, a⁻¹] : Matrix (Fin 2) (Fin 2) ℂ).det = 1 := by
  simp [Matrix.det_fin_two_of, ha]

theorem uinv_actP_transl (x : ℂ) : UInv (actP !![1, x; 0, 1]) :=
  (uinv_transl x).congr fun p _ => (uhsAct_transl x p.1 p.2).symm

theorem uinv_actP_diag {a : ℂ} (ha : a ≠ 0) : UInv (actP !![a, 0; 0, a⁻¹]) :=
  (uinv_diag ha).congr fun p _ => (uhsAct_diag ha p.1 p.2).symm

theorem UInv.mul {g h : Matrix (Fin 2) (Fin 2) ℂ} (hg : g.det = 1) (hh : h.det = 1)
    (hug : UInv (actP g)) (huh : UInv (actP h)) : UInv (actP (g * h)) :=
  (hug.comp huh).congr fun _ hp => (actP_mul hg hh hp).symm

/-- **The measure `dz dv/v³` is invariant under `SL_2(ℂ)`**: every `g` of determinant `1` is
`T·E·D·T` (or `D·T` when its lower-left entry vanishes). -/
theorem uinv_actP {g : Matrix (Fin 2) (Fin 2) ℂ} (hg : g.det = 1) : UInv (actP g) := by
  have hdet := det_two_eq_one g hg
  by_cases hc : g 1 0 = 0
  · have ha : g 0 0 ≠ 0 := fun h => by rw [h, hc] at hdet; simp at hdet
    have e : g = !![g 0 0, 0; 0, (g 0 0)⁻¹] * !![1, g 0 1 / g 0 0; 0, 1] := by
      have hd : g 1 1 = (g 0 0)⁻¹ := by
        rw [hc, mul_zero, sub_zero] at hdet; exact eq_inv_of_mul_eq_one_right hdet
      ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, hc, hd]
      field_simp
    rw [e]
    exact UInv.mul (det_diag ha) (det_transl _) (uinv_actP_diag ha) (uinv_actP_transl _)
  · have e : g = !![1, g 0 0 / g 1 0; 0, 1] * !![0, -1; 1, 0] * !![g 1 0, 0; 0, (g 1 0)⁻¹] *
        !![1, g 1 1 / g 1 0; 0, 1] := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply] <;> field_simp
      linear_combination -hdet
    rw [e]
    have h1 : (!![1, g 0 0 / g 1 0; 0, 1] * !![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ).det = 1 := by
      rw [Matrix.det_mul, det_transl, det_E, one_mul]
    have h2 : (!![1, g 0 0 / g 1 0; 0, 1] * !![0, -1; 1, 0] * !![g 1 0, 0; 0, (g 1 0)⁻¹] :
        Matrix (Fin 2) (Fin 2) ℂ).det = 1 := by
      rw [Matrix.det_mul, h1, det_diag hc, one_mul]
    exact UInv.mul h2 (det_transl _)
      (UInv.mul h1 (det_diag hc) (UInv.mul (det_transl _) det_E (uinv_actP_transl _) uinv_actP_E)
        (uinv_actP_diag hc)) (uinv_actP_transl _)

/-- **The invariant measure** `dz dv/v³` on upper half-space `{v > 0} ⊂ ℂ × ℝ`. -/
def uhsMeasure : Measure (ℂ × ℝ) := (volume.restrict UHS).withDensity uhsW

theorem measurable_uhsW : Measurable uhsW := by unfold uhsW; fun_prop

theorem lintegral_uhsMeasure {F : ℂ × ℝ → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ p, F p ∂uhsMeasure = ∫⁻ p in UHS, F p * uhsW p := by
  rw [uhsMeasure, lintegral_withDensity_eq_lintegral_mul _ measurable_uhsW hF]
  simp only [Pi.mul_apply, mul_comm]

theorem measurable_actP (g : Matrix (Fin 2) (Fin 2) ℂ) : Measurable (actP g) := by
  unfold actP uhsAct uhsZ uhsV uhsDen
  fun_prop

/-- **The action of `SL_2(ℂ)` preserves `dz dv/v³`.** -/
theorem measurePreserving_actP {g : Matrix (Fin 2) (Fin 2) ℂ} (hg : g.det = 1) :
    MeasurePreserving (actP g) uhsMeasure uhsMeasure := by
  refine ⟨measurable_actP g, ?_⟩
  ext A hA
  rw [Measure.map_apply (measurable_actP g) hA, ← lintegral_indicator_one hA,
    ← lintegral_indicator_one ((measurable_actP g) hA),
    lintegral_uhsMeasure (measurable_one.indicator ((measurable_actP g) hA)),
    lintegral_uhsMeasure (measurable_one.indicator hA)]
  exact uinv_actP hg (A.indicator 1)

theorem lintegral_actP {g : Matrix (Fin 2) (Fin 2) ℂ} (hg : g.det = 1) {F : ℂ × ℝ → ℝ≥0∞}
    (hF : Measurable F) : ∫⁻ p, F (actP g p) ∂uhsMeasure = ∫⁻ p, F p ∂uhsMeasure :=
  (measurePreserving_actP hg).lintegral_comp hF

theorem integral_actP {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : Matrix (Fin 2) (Fin 2) ℂ} (hg : g.det = 1) {F : ℂ × ℝ → E}
    (hF : AEStronglyMeasurable F uhsMeasure) :
    ∫ p, F (actP g p) ∂uhsMeasure = ∫ p, F p ∂uhsMeasure := by
  have h := measurePreserving_actP hg
  rw [← integral_map (measurable_actP g).aemeasurable (by rwa [h.map_eq]), h.map_eq]

end Eis

#print axioms Eis.det_inversion_deriv
#print axioms Eis.e3_apply
#print axioms Eis.norm_e3_sq
#print axioms Eis.measurableSet_UHS
#print axioms Eis.lintegral_UHS_comp
#print axioms Eis.psiInv_apply
#print axioms Eis.e3_ne_zero
#print axioms Eis.hasFDerivAt_psiInv
#print axioms Eis.det_psiInv
#print axioms Eis.UInv.comp
#print axioms Eis.UInv.congr
#print axioms Eis.uinv_of_jac
#print axioms Eis.image_eq_of_invol
#print axioms Eis.psiInv_psiInv
#print axioms Eis.rsq_pos
#print axioms Eis.psiInv_snd
#print axioms Eis.uinv_psiInv
#print axioms Eis.tauL_apply
#print axioms Eis.det_tauL
#print axioms Eis.uinv_tauR
#print axioms Eis.uinv_transl
#print axioms Eis.actP_mul
#print axioms Eis.actP_mem
#print axioms Eis.uhsAct_diag
#print axioms Eis.diagL_apply
#print axioms Eis.det_diagL
#print axioms Eis.uinv_diag
#print axioms Eis.uinv_actP_E
#print axioms Eis.det_transl
#print axioms Eis.det_E
#print axioms Eis.det_diag
#print axioms Eis.uinv_actP_transl
#print axioms Eis.uinv_actP_diag
#print axioms Eis.UInv.mul
#print axioms Eis.uinv_actP
#print axioms Eis.measurable_uhsW
#print axioms Eis.lintegral_uhsMeasure
#print axioms Eis.measurable_actP
#print axioms Eis.measurePreserving_actP
#print axioms Eis.lintegral_actP
#print axioms Eis.integral_actP
