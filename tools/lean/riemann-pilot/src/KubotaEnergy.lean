import KubotaMeasure

/-! # The conformality of the action, and the invariant energy (round 384)

S5f-8 of round 360's plan, part 2. Round 383 proved that `dz dv/v³` is invariant under `SL_2(ℂ)`. This
file proves that the action is conformal, with factor `v(g·p)/v(p)`, and that the hyperbolic energy
`∫ v²|∇F|² dz dv/v³` is invariant. Round 360's S5f-10 plans Lax–Milgram for this energy form.

* **The energy density** (`edens`, a definition; `edens_eq_sum`, `sum_sq_norm_map_basis`,
  `sum_sq_norm_isometry`): `edens L = |L(1, 0)|² + |L(i, 0)|² + |L(0, 1)|²`, the squared Hilbert–Schmidt
  norm in the coordinates `(Re z, Im z, v)`. It does not depend on the orthonormal basis of `ℝ³`: for
  real and imaginary parts, Mathlib's Riesz representation (`toDual_symm_apply`) and Parseval
  (`OrthonormalBasis.sum_sq_inner_right`).
* **Conformal maps** (`Conf`, a definition; `edens_comp_conformal`, `Conf.comp`, `Conf.congr`): a
  derivative `c·(e3⁻¹ R e3)` with `R` an isometry of `ℝ³` scales `edens` by `c²`. `Conf f` says that `f`
  has such a derivative at every `p` with `v > 0`, with `c = v(f(p))/v(p)`; it is closed under composition.
* **The generators** (`conf_psiInv`, `conf_tauR`, `conf_transl`, `conf_diag`, with `edens_comp_tauL`,
  `edens_comp_diagL` and `norm_rot_sq`): the inversion `ψ` (Mathlib's derivative of the inversion is
  `‖x‖⁻²` times a reflection), `τ`, the translations, and `(z, v) ↦ (a²z, |a|²v)`.
* **Every `g` of determinant `1`** (**`conf_actP`**, with `actP_E_eq`, `conf_actP_E` and `Conf.mul`):
  the decomposition of round 383.
* **The energy** (**`edens_actP`**, **`lintegral_energy_actP`**, `edens_smul`, **`edens_automorphic`**):
  `v(p)²·edens((F∘g)′(p)) = v(g·p)²·edens(F′(g·p))`, so with round 383's invariance of the measure
  `∫ v²·edens(F′) dz dv/v³` is invariant under `F ↦ F∘g`. For `F(g·p) = c·F(p)` with `|c| = 1`, the
  density `v²·edens(F′)` is invariant.
-/

open MeasureTheory Set Module Filter
open scoped ENNReal ComplexConjugate RealInnerProductSpace Topology

noncomputable section

namespace Eis

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **The energy density** of a real-linear map `L : ℂ × ℝ → ℂ`: `|L(1, 0)|² + |L(i, 0)|² + |L(0, 1)|²`,
the squared Hilbert–Schmidt norm in the coordinates `(Re z, Im z, v)`. -/
def edens (L : ℂ × ℝ →L[ℝ] ℂ) : ℝ := ‖L (1, 0)‖ ^ 2 + ‖L (Complex.I, 0)‖ ^ 2 + ‖L (0, 1)‖ ^ 2

/-- **Parseval for a complex-valued functional**: `Σ_i |L(b_i)|²` does not depend on the orthonormal
basis `b` of `ℝ³`. -/
theorem sum_sq_norm_map_basis (L : E3 →L[ℝ] ℂ) (b : OrthonormalBasis (Fin 3) ℝ E3) :
    ∑ i, ‖L (b i)‖ ^ 2 =
      ‖(InnerProductSpace.toDual ℝ E3).symm (Complex.reCLM.comp L)‖ ^ 2 +
        ‖(InnerProductSpace.toDual ℝ E3).symm (Complex.imCLM.comp L)‖ ^ 2 := by
  rw [← b.sum_sq_inner_right ((InnerProductSpace.toDual ℝ E3).symm (Complex.reCLM.comp L)),
    ← b.sum_sq_inner_right ((InnerProductSpace.toDual ℝ E3).symm (Complex.imCLM.comp L)),
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [real_inner_comm, InnerProductSpace.toDual_symm_apply, real_inner_comm,
    InnerProductSpace.toDual_symm_apply, Complex.sq_norm, Complex.normSq_apply]
  simp only [ContinuousLinearMap.comp_apply, Complex.reCLM_apply, Complex.imCLM_apply]
  ring

theorem sum_sq_norm_isometry (L : E3 →L[ℝ] ℂ) (R : E3 ≃ₗᵢ[ℝ] E3) :
    ∑ i, ‖L (R (EuclideanSpace.basisFun (Fin 3) ℝ i))‖ ^ 2 =
      ∑ i, ‖L (EuclideanSpace.basisFun (Fin 3) ℝ i)‖ ^ 2 := by
  rw [sum_sq_norm_map_basis L (EuclideanSpace.basisFun (Fin 3) ℝ)]
  rw [← sum_sq_norm_map_basis L ((EuclideanSpace.basisFun (Fin 3) ℝ).map R)]
  rfl

theorem e3_symm_single (i : Fin 3) :
    e3.symm (EuclideanSpace.single i (1 : ℝ)) = ![((1 : ℂ), (0 : ℝ)), (Complex.I, 0), (0, 1)] i := by
  apply e3.injective
  rw [ContinuousLinearEquiv.apply_symm_apply, e3_apply]
  ext j
  fin_cases i <;> fin_cases j <;> simp

theorem edens_eq_sum (L : ℂ × ℝ →L[ℝ] ℂ) :
    edens L = ∑ i, ‖(L.comp (e3.symm : E3 →L[ℝ] ℂ × ℝ)) (EuclideanSpace.basisFun (Fin 3) ℝ i)‖ ^ 2 := by
  rw [Fin.sum_univ_three, edens]
  simp only [ContinuousLinearMap.comp_apply, EuclideanSpace.basisFun_apply]
  rw [ContinuousLinearEquiv.coe_coe, e3_symm_single, e3_symm_single, e3_symm_single]
  rfl

/-- **A conformal derivative scales the energy density**: for an isometry `R` of `ℝ³` and `c ∈ ℝ`,
`edens (L ∘ c·(e3⁻¹ R e3)) = c²·edens L`. -/
theorem edens_comp_conformal (L : ℂ × ℝ →L[ℝ] ℂ) (c : ℝ) (R : E3 ≃ₗᵢ[ℝ] E3) :
    edens (L.comp (c • (e3.symm : E3 →L[ℝ] ℂ × ℝ).comp ((R : E3 →L[ℝ] E3).comp (e3 : ℂ × ℝ →L[ℝ] E3)))) =
      c ^ 2 * edens L := by
  rw [edens_eq_sum, edens_eq_sum, ← sum_sq_norm_isometry (L.comp (e3.symm : E3 →L[ℝ] ℂ × ℝ)) R,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [ContinuousLinearMap.comp_apply, smul_apply, map_smul,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply, norm_smul, mul_pow,
    Real.norm_eq_abs, sq_abs]
  rfl

theorem isOpen_UHS : IsOpen UHS := isOpen_lt continuous_const continuous_snd

/-- **Conformal maps of upper half-space**: differentiable on `{v > 0}`, with
`edens (L ∘ f′(p)) = (v(f(p))/v(p))²·edens L`. -/
def Conf (f : ℂ × ℝ → ℂ × ℝ) : Prop :=
  ∀ p ∈ UHS, ∃ D : ℂ × ℝ →L[ℝ] ℂ × ℝ, HasFDerivAt f D p ∧
    ∀ L : ℂ × ℝ →L[ℝ] ℂ, edens (L.comp D) = ((f p).2 / p.2) ^ 2 * edens L

theorem Conf.comp {f g : ℂ × ℝ → ℂ × ℝ} (hf : Conf f) (hg : Conf g) (hgU : ∀ p ∈ UHS, g p ∈ UHS) :
    Conf (f ∘ g) := fun p hp => by
  obtain ⟨Dg, hDg, hg'⟩ := hg p hp
  obtain ⟨Df, hDf, hf'⟩ := hf (g p) (hgU p hp)
  refine ⟨Df.comp Dg, hDf.comp p hDg, fun L => ?_⟩
  have hgp : (0 : ℝ) < (g p).2 := hgU p hp
  have hp' : (0 : ℝ) < p.2 := hp
  rw [← ContinuousLinearMap.comp_assoc, hg', hf', Function.comp_apply]
  field_simp

theorem Conf.congr {f g : ℂ × ℝ → ℂ × ℝ} (hf : Conf f) (h : ∀ p ∈ UHS, f p = g p) : Conf g :=
  fun p hp => by
    obtain ⟨D, hD, hD'⟩ := hf p hp
    refine ⟨D, hD.congr_of_eventuallyEq ?_, fun L => by rw [hD' L, h p hp]⟩
    filter_upwards [isOpen_UHS.mem_nhds hp] with q hq using (h q hq).symm

/-- **The inversion is conformal**, with factor `1/(|z|² + v²)`. -/
theorem conf_psiInv : Conf psiInv := fun p hp => by
  refine ⟨_, hasFDerivAt_psiInv hp, fun L => ?_⟩
  have e : (e3.symm : E3 →L[ℝ] ℂ × ℝ).comp
      (((1 / dist (e3 p) 0) ^ 2 • ((ℝ ∙ (e3 p - 0))ᗮ.reflection : E3 →L[ℝ] E3)).comp
        (e3 : ℂ × ℝ →L[ℝ] E3)) =
      ((1 / dist (e3 p) 0) ^ 2) • (e3.symm : E3 →L[ℝ] ℂ × ℝ).comp
        ((((ℝ ∙ (e3 p - 0))ᗮ.reflection : E3 ≃ₗᵢ[ℝ] E3) : E3 →L[ℝ] E3).comp (e3 : ℂ × ℝ →L[ℝ] E3)) := by
    rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]
  rw [e, edens_comp_conformal, psiInv_snd, dist_zero_right, div_pow, one_pow, norm_e3_sq]
  have hv : (0 : ℝ) < p.2 := hp
  congr 1
  field_simp

theorem edens_comp_tauL (L : ℂ × ℝ →L[ℝ] ℂ) : edens (L.comp tauL) = edens L := by
  unfold edens
  simp only [ContinuousLinearMap.comp_apply, tauL_apply, tauR, map_one, map_zero, neg_zero,
    Complex.conj_I, neg_neg]
  have : ((-1 : ℂ), (0 : ℝ)) = -((1 : ℂ), (0 : ℝ)) := by ext <;> simp
  rw [this, map_neg, norm_neg]

theorem conf_tauR : Conf tauR := fun p _ => by
  refine ⟨tauL, ?_, fun L => ?_⟩
  · have : tauR = tauL := funext tauL_apply |>.symm
    rw [this]; exact tauL.hasFDerivAt
  · have hv : p.2 ≠ 0 := (show (0 : ℝ) < p.2 from ‹_›).ne'
    rw [edens_comp_tauL]; simp [tauR, hv]

theorem conf_transl (b : ℂ) : Conf (fun p : ℂ × ℝ => (p.1 + b, p.2)) := fun p hp => by
  refine ⟨ContinuousLinearMap.id ℝ (ℂ × ℝ), ?_, fun L => ?_⟩
  · have h : (fun p : ℂ × ℝ => (p.1 + b, p.2)) = fun p => p + (b, 0) := by funext p; ext <;> simp
    rw [h]; exact (hasFDerivAt_id p).add_const _
  · have hv : p.2 ≠ 0 := (show (0 : ℝ) < p.2 from hp).ne'
    simp [hv]

/-- `‖αX + βY‖² + ‖−βX + αY‖² = (α² + β²)(‖X‖² + ‖Y‖²)`. -/
theorem norm_rot_sq (α β : ℝ) (X Y : ℂ) :
    ‖(α : ℂ) * X + β * Y‖ ^ 2 + ‖-(β : ℂ) * X + α * Y‖ ^ 2 = (α ^ 2 + β ^ 2) * (‖X‖ ^ 2 + ‖Y‖ ^ 2) := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.neg_re, Complex.neg_im]
  ring

theorem edens_comp_diagL (a : ℂ) (L : ℂ × ℝ →L[ℝ] ℂ) :
    edens (L.comp (diagL a)) = Complex.normSq a ^ 2 * edens L := by
  unfold edens
  simp only [ContinuousLinearMap.comp_apply, diagL_apply, mul_one, mul_zero]
  set α := (a ^ 2).re
  set β := (a ^ 2).im
  have h1 : ((a ^ 2 : ℂ), (0 : ℝ)) = α • ((1 : ℂ), (0 : ℝ)) + β • (Complex.I, (0 : ℝ)) := by
    ext <;> simp [α, β]
  have h2 : ((a ^ 2 * Complex.I : ℂ), (0 : ℝ)) = (-β) • ((1 : ℂ), (0 : ℝ)) + α • (Complex.I, (0 : ℝ)) := by
    ext
    · apply Complex.ext <;> simp [α, β]
    · simp
  have h3 : ((0 : ℂ), Complex.normSq a) = Complex.normSq a • ((0 : ℂ), (1 : ℝ)) := by ext <;> simp
  rw [h1, h2, h3, map_add, map_add, map_smul, map_smul, map_smul, map_smul, map_smul]
  simp only [Complex.real_smul]
  have hαβ : α ^ 2 + β ^ 2 = Complex.normSq a ^ 2 := by
    rw [← map_pow, Complex.normSq_apply]; ring
  rw [show ((-β : ℝ) : ℂ) = -(β : ℂ) by push_cast; ring, norm_rot_sq, hαβ, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, mul_pow, sq_abs]
  ring

theorem conf_diag (a : ℂ) :
    Conf (fun p : ℂ × ℝ => (a ^ 2 * p.1, Complex.normSq a * p.2)) := fun p hp => by
  refine ⟨diagL a, ?_, fun L => ?_⟩
  · have : (fun p : ℂ × ℝ => (a ^ 2 * p.1, Complex.normSq a * p.2)) = diagL a := funext fun p => rfl
    rw [this]; exact (diagL a).hasFDerivAt
  · have hv : p.2 ≠ 0 := (show (0 : ℝ) < p.2 from hp).ne'
    rw [edens_comp_diagL]; congr 1; field_simp

theorem psiInv_mem {p : ℂ × ℝ} (hp : p ∈ UHS) : psiInv p ∈ UHS := by
  show 0 < (psiInv p).2
  rw [psiInv_snd]; exact mul_pos (inv_pos.2 (rsq_pos hp)) hp

theorem actP_E_eq (p : ℂ × ℝ) : actP !![0, -1; 1, 0] p = tauR (psiInv p) := by
  simp only [actP, uhsAct_inv, tauR, psiInv_apply, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  refine Prod.ext ?_ ?_
  · simp only
    rw [Complex.real_smul, map_mul, Complex.conj_ofReal, div_eq_mul_inv, Complex.ofReal_inv]
    ring
  · simp only; rw [div_eq_mul_inv]; ring

theorem conf_actP_transl (x : ℂ) : Conf (actP !![1, x; 0, 1]) :=
  (conf_transl x).congr fun p _ => (uhsAct_transl x p.1 p.2).symm

theorem conf_actP_diag {a : ℂ} (ha : a ≠ 0) : Conf (actP !![a, 0; 0, a⁻¹]) :=
  (conf_diag a).congr fun p _ => (uhsAct_diag ha p.1 p.2).symm

theorem conf_actP_E : Conf (actP !![0, -1; 1, 0]) :=
  (conf_tauR.comp conf_psiInv fun _ hp => psiInv_mem hp).congr fun p _ => (actP_E_eq p).symm

theorem Conf.mul {g h : Matrix (Fin 2) (Fin 2) ℂ} (hg : g.det = 1) (hh : h.det = 1)
    (hcg : Conf (actP g)) (hch : Conf (actP h)) : Conf (actP (g * h)) :=
  (hcg.comp hch fun _ hp => actP_mem hh hp).congr fun _ hp => (actP_mul hg hh hp).symm

/-- **The action of `SL_2(ℂ)` on upper half-space is conformal**, with factor `v(g·p)/v(p)`. -/
theorem conf_actP {g : Matrix (Fin 2) (Fin 2) ℂ} (hg : g.det = 1) : Conf (actP g) := by
  have hdet := det_two_eq_one g hg
  by_cases hc : g 1 0 = 0
  · have ha : g 0 0 ≠ 0 := fun h => by rw [h, hc] at hdet; simp at hdet
    have e : g = !![g 0 0, 0; 0, (g 0 0)⁻¹] * !![1, g 0 1 / g 0 0; 0, 1] := by
      have hd : g 1 1 = (g 0 0)⁻¹ := by
        rw [hc, mul_zero, sub_zero] at hdet; exact eq_inv_of_mul_eq_one_right hdet
      ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, hc, hd]
      field_simp
    rw [e]
    exact Conf.mul (det_diag ha) (det_transl _) (conf_actP_diag ha) (conf_actP_transl _)
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
    exact Conf.mul h2 (det_transl _)
      (Conf.mul h1 (det_diag hc) (Conf.mul (det_transl _) det_E (conf_actP_transl _) conf_actP_E)
        (conf_actP_diag hc)) (conf_actP_transl _)

/-- **The hyperbolic energy density transforms by the action**: for `F` differentiable at `g·p`,
`v(p)²·edens((F∘g)′(p)) = v(g·p)²·edens(F′(g·p))`. -/
theorem edens_actP {g : Matrix (Fin 2) (Fin 2) ℂ} (hg : g.det = 1) {F : ℂ × ℝ → ℂ} {p : ℂ × ℝ}
    (hp : p ∈ UHS) (hF : DifferentiableAt ℝ F (actP g p)) :
    p.2 ^ 2 * edens (fderiv ℝ (F ∘ actP g) p) = (actP g p).2 ^ 2 * edens (fderiv ℝ F (actP g p)) := by
  obtain ⟨D, hD, hD'⟩ := conf_actP hg p hp
  rw [(hF.hasFDerivAt.comp p hD).fderiv, hD']
  have hv : (0 : ℝ) < p.2 := hp
  field_simp

/-- **The energy `∫ v²·edens(F′) dz dv/v³` is invariant under `SL_2(ℂ)`**, for `F` differentiable on
`{v > 0}`. -/
theorem lintegral_energy_actP {g : Matrix (Fin 2) (Fin 2) ℂ} (hg : g.det = 1) {F : ℂ × ℝ → ℂ}
    (hF : ∀ p ∈ UHS, DifferentiableAt ℝ F p) :
    ∫⁻ p in UHS, ENNReal.ofReal (p.2 ^ 2 * edens (fderiv ℝ (F ∘ actP g) p)) * uhsW p =
      ∫⁻ p in UHS, ENNReal.ofReal (p.2 ^ 2 * edens (fderiv ℝ F p)) * uhsW p := by
  calc ∫⁻ p in UHS, ENNReal.ofReal (p.2 ^ 2 * edens (fderiv ℝ (F ∘ actP g) p)) * uhsW p
      = ∫⁻ p in UHS, (fun q => ENNReal.ofReal (q.2 ^ 2 * edens (fderiv ℝ F q))) (actP g p) * uhsW p :=
        setLIntegral_congr_fun measurableSet_UHS fun p hp => by
          rw [edens_actP hg hp (hF _ (actP_mem hg hp))]
    _ = _ := uinv_actP hg (fun q => ENNReal.ofReal (q.2 ^ 2 * edens (fderiv ℝ F q)))

theorem edens_smul (c : ℂ) (L : ℂ × ℝ →L[ℝ] ℂ) : edens (c • L) = ‖c‖ ^ 2 * edens L := by
  simp only [edens, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow]
  ring

/-- **The energy density of an automorphic function is invariant**: if `F(g·p) = c·F(p)` on `{v > 0}`
with `|c| = 1`, then `v(g·p)²·edens(F′(g·p)) = v(p)²·edens(F′(p))`. -/
theorem edens_automorphic {g : Matrix (Fin 2) (Fin 2) ℂ} (hg : g.det = 1) {F : ℂ × ℝ → ℂ} {c : ℂ}
    (hc : ‖c‖ = 1) (hFg : ∀ p ∈ UHS, F (actP g p) = c * F p) {p : ℂ × ℝ} (hp : p ∈ UHS)
    (hF : DifferentiableAt ℝ F p) (hF' : DifferentiableAt ℝ F (actP g p)) :
    (actP g p).2 ^ 2 * edens (fderiv ℝ F (actP g p)) = p.2 ^ 2 * edens (fderiv ℝ F p) := by
  rw [← edens_actP hg hp hF']
  have e : fderiv ℝ (F ∘ actP g) p = fderiv ℝ (fun q => c * F q) p := by
    refine Filter.EventuallyEq.fderiv_eq ?_
    filter_upwards [isOpen_UHS.mem_nhds hp] with q hq using hFg q hq
  rw [e, fderiv_const_mul hF c, edens_smul, hc, one_pow, one_mul]

end Eis

#print axioms Eis.sum_sq_norm_map_basis
#print axioms Eis.sum_sq_norm_isometry
#print axioms Eis.e3_symm_single
#print axioms Eis.edens_eq_sum
#print axioms Eis.edens_comp_conformal
#print axioms Eis.isOpen_UHS
#print axioms Eis.Conf.comp
#print axioms Eis.Conf.congr
#print axioms Eis.conf_psiInv
#print axioms Eis.edens_comp_tauL
#print axioms Eis.conf_tauR
#print axioms Eis.conf_transl
#print axioms Eis.norm_rot_sq
#print axioms Eis.edens_comp_diagL
#print axioms Eis.conf_diag
#print axioms Eis.psiInv_mem
#print axioms Eis.actP_E_eq
#print axioms Eis.conf_actP_transl
#print axioms Eis.conf_actP_diag
#print axioms Eis.conf_actP_E
#print axioms Eis.Conf.mul
#print axioms Eis.conf_actP
#print axioms Eis.edens_actP
#print axioms Eis.lintegral_energy_actP
#print axioms Eis.edens_smul
#print axioms Eis.edens_automorphic
