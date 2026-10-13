import KubotaBallCount
import HilbertResolvent

/-! # The ball average as a self-adjoint operator (round 421)

S5f-10 of round 360's plan, part 4 (S5f-10b, second half, second part). For a subgroup `Γ` of `SL_2(ℤ[ω])`
with a unitary character `χ` and a partition of unity `ρ` (round 386's `IsPU`), this round constructs the
operator of round 418's plan on `L²(ν)`, `ν = ρ dμ`, and proves it self-adjoint, so that round 419's
resolvent facts apply to it.

* **Unitary characters** (`IsUChar`, a structure; `IsUChar.map_one` and **`IsUChar.map_inv`**):
  multiplicative on `Γ` with `|χ| = 1`, so `χ(γ⁻¹) = conj χ(γ)`.
* **The kernel** (`bker`, a definition; **`enorm_bker_le`** and **`bker_swap`**, with
  `measurable_hball_indC` and `measurable_bker`): `k(p, q) = Σ_γ χ(γ)·1_{B_R(p)}(γq)` is measurable,
  `|k(p, q)| ≤ N(p, q)` (round 420's counting function, Mathlib's `enorm_tsum_le_tsum_enorm`), and
  `k(q, p) = conj k(p, q)` on upper half-space, by reindexing `γ ↦ γ⁻¹` and round 420's
  `mem_hball_slAct_iff`.
* **The form** (`bformF` and `bform`, definitions; **`norm_bform_le`**, with `lintegral_enorm_sq_rpow`,
  `measurable_bformF`, `lintegral_bformF_le` and `integrable_bformF`):
  `B(f, g) = ∫conj k(p, q)·conj f(q)·g(p) d(ν ⊗ ν)` for `f, g ∈ L²(ν)`, with `|B(f, g)| ≤ V_R‖f‖‖g‖` by
  round 420's Schur bound, for `R ≥ 0`.
* **The operator** (`bformCLM` and `ballOp`, definitions; **`inner_ballOp`**, with `ae_snd_add`,
  `ae_fst_add`, `ae_snd_smul`, `ae_fst_smul`, `bform_add_left`, `bform_smul_left`, `bform_add_right` and
  `bform_smul_right`): `B` is conjugate-linear in `f` and linear in `g`, and `K = ballOp` has
  `⟪Kf, g⟫ = B(f, g)` (Mathlib's `InnerProductSpace.continuousLinearMapOfBilin`).
* **Self-adjointness** (**`isSelfAdjoint_ballOp`**, with `ae_prod_UHS` and `bform_eq_conj`):
  `B(f, g) = conj B(g, f)`, by swapping the coordinates of `ν ⊗ ν` (Mathlib's `integral_prod_swap`) and
  `bker_swap`.
-/

open MeasureTheory Set Filter NumberField
open scoped ENNReal ComplexConjugate MatrixGroups InnerProductSpace

noncomputable section

namespace Eis

/-! ### Unitary characters -/

/-- `χ` is a unitary character on `Γ`. -/
structure IsUChar (Γ : Subgroup SL(2, 𝓞 K)) (χ : SL(2, 𝓞 K) → ℂ) : Prop where
  map_mul : ∀ g ∈ Γ, ∀ h ∈ Γ, χ (g * h) = χ g * χ h
  norm_eq : ∀ g ∈ Γ, ‖χ g‖ = 1

variable {Γ : Subgroup SL(2, 𝓞 K)} {χ : SL(2, 𝓞 K) → ℂ}

theorem IsUChar.map_one (hχ : IsUChar Γ χ) : χ 1 = 1 := by
  have h1 := hχ.map_mul 1 Γ.one_mem 1 Γ.one_mem
  rw [mul_one] at h1
  have hne : χ 1 ≠ 0 := by
    intro h0
    have := hχ.norm_eq 1 Γ.one_mem
    rw [h0, norm_zero] at this
    exact zero_ne_one this
  exact mul_left_cancel₀ hne (h1.symm.trans (mul_one _).symm)

theorem IsUChar.map_inv (hχ : IsUChar Γ χ) {g : SL(2, 𝓞 K)} (hg : g ∈ Γ) :
    χ g⁻¹ = conj (χ g) := by
  have h1 := hχ.map_mul g hg g⁻¹ (Γ.inv_mem hg)
  rw [mul_inv_cancel, hχ.map_one] at h1
  have h2 : conj (χ g) * χ g = 1 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hχ.norm_eq g hg]; simp
  calc χ g⁻¹ = (conj (χ g) * χ g) * χ g⁻¹ := by rw [h2, one_mul]
    _ = conj (χ g) * (χ g * χ g⁻¹) := by ring
    _ = conj (χ g) := by rw [← h1, mul_one]

/-! ### The kernel -/

/-- The kernel `k(p, q) = Σ_γ χ(γ)·1_{B_R(p)}(γq)`. -/
def bker (Γ : Subgroup SL(2, 𝓞 K)) (χ : SL(2, 𝓞 K) → ℂ) (R : ℝ) (p q : ℂ × ℝ) : ℂ :=
  ∑' γ : Γ, χ γ * (hball R p).indicator 1 (slAct γ q)

theorem measurable_hball_indC (R : ℝ) (γ : SL(2, 𝓞 K)) :
    Measurable fun x : (ℂ × ℝ) × (ℂ × ℝ) =>
      (hball R x.1).indicator (1 : ℂ × ℝ → ℂ) (slAct γ x.2) := by
  set S : Set ((ℂ × ℝ) × (ℂ × ℝ)) := {x | slAct γ x.2 ∈ UHS ∧ ppi x.1 (slAct γ x.2) ≤ R}
  have hS : MeasurableSet S :=
    (measurableSet_UHS.preimage ((measurable_slAct γ).comp measurable_snd)).inter
      (measurableSet_le (measurable_ppi₂.comp (measurable_fst.prodMk
        ((measurable_slAct γ).comp measurable_snd))) measurable_const)
  have e : (fun x : (ℂ × ℝ) × (ℂ × ℝ) => (hball R x.1).indicator (1 : ℂ × ℝ → ℂ) (slAct γ x.2)) =
      S.indicator 1 := by
    funext x
    by_cases h : slAct γ x.2 ∈ hball R x.1
    · rw [indicator_of_mem h, indicator_of_mem (show x ∈ S from h)]; rfl
    · rw [indicator_of_notMem h, indicator_of_notMem (show x ∉ S from h)]
  rw [e]
  exact measurable_one.indicator hS

theorem measurable_bker (Γ : Subgroup SL(2, 𝓞 K)) (χ : SL(2, 𝓞 K) → ℂ) (R : ℝ) :
    Measurable fun x : (ℂ × ℝ) × (ℂ × ℝ) => bker Γ χ R x.1 x.2 :=
  Measurable.tsum fun γ => measurable_const.mul (measurable_hball_indC R γ)

/-- `|k(p, q)| ≤ N(p, q)`. -/
theorem enorm_bker_le (hχ : IsUChar Γ χ) (R : ℝ) (p q : ℂ × ℝ) :
    ‖bker Γ χ R p q‖ₑ ≤ cntB Γ R p q := by
  refine enorm_tsum_le_tsum_enorm.trans (le_of_eq (tsum_congr fun γ => ?_))
  rw [enorm_mul, ← ofReal_norm, hχ.norm_eq γ γ.2, ENNReal.ofReal_one, one_mul]
  by_cases h : slAct γ q ∈ hball R p
  · rw [indicator_of_mem h, indicator_of_mem h]; simp
  · rw [indicator_of_notMem h, indicator_of_notMem h]; simp

/-- **The kernel is Hermitian**: `k(q, p) = conj k(p, q)` on upper half-space. -/
theorem bker_swap (hχ : IsUChar Γ χ) (R : ℝ) {p q : ℂ × ℝ} (hp : p ∈ UHS) (hq : q ∈ UHS) :
    bker Γ χ R q p = conj (bker Γ χ R p q) := by
  unfold bker
  rw [Complex.conj_tsum, ← (Equiv.inv Γ).tsum_eq]
  refine tsum_congr fun γ => ?_
  simp only [Equiv.inv_apply, Subgroup.coe_inv, map_mul]
  rw [hχ.map_inv γ.2]
  have hiff := mem_hball_slAct_iff (γ : SL(2, 𝓞 K)) (R := R) hp hq
  by_cases h : slAct γ q ∈ hball R p
  · rw [indicator_of_mem h, indicator_of_mem (hiff.1 h)]; simp
  · rw [indicator_of_notMem h, indicator_of_notMem fun h' => h (hiff.2 h')]; simp

/-! ### The form on `L²(ν)` -/

section Form

variable {ρ : ℂ × ℝ → ℝ≥0∞}

/-- `(∫‖f‖² dν)^{1/2} = ‖f‖₂` as an extended number. -/
theorem lintegral_enorm_sq_rpow (f : Lp ℂ 2 (muR ρ)) :
    (∫⁻ x, ‖f x‖ₑ ^ 2 ∂(muR ρ)) ^ (1 / 2 : ℝ) = eLpNorm f 2 (muR ρ) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top
    (Lp.aestronglyMeasurable f)]
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two]

/-- The integrand of the form: `conj k(p, q)·conj f(q)·g(p)` at `x = (p, q)`. -/
def bformF (Γ : Subgroup SL(2, 𝓞 K)) (χ : SL(2, 𝓞 K) → ℂ) (R : ℝ) (f g : ℂ × ℝ → ℂ)
    (x : (ℂ × ℝ) × (ℂ × ℝ)) : ℂ :=
  conj (bker Γ χ R x.1 x.2) * (conj (f x.2) * g x.1)

theorem measurable_bformF (Γ : Subgroup SL(2, 𝓞 K)) (χ : SL(2, 𝓞 K) → ℂ) (R : ℝ)
    (f g : Lp ℂ 2 (muR ρ)) : Measurable (bformF Γ χ R f g) := by
  have hk := measurable_bker Γ χ R
  have hf := (Lp.stronglyMeasurable f).measurable
  have hg := (Lp.stronglyMeasurable g).measurable
  unfold bformF
  exact (Complex.continuous_conj.measurable.comp hk).mul
    ((Complex.continuous_conj.measurable.comp (hf.comp measurable_snd)).mul (hg.comp measurable_fst))

/-- **The bound on the integrand**: `∫|conj k·conj f(q)·g(p)| ≤ V_R·‖g‖₂‖f‖₂`. -/
theorem lintegral_bformF_le {ρ : ℂ × ℝ → ℝ≥0∞} (hρ : IsPU Γ ρ) (hχ : IsUChar Γ χ) (R : ℝ)
    (f g : Lp ℂ 2 (muR ρ)) :
    ∫⁻ x, ‖bformF Γ χ R f g x‖ₑ ∂((muR ρ).prod (muR ρ)) ≤
      VB R * (eLpNorm g 2 (muR ρ) * eLpNorm f 2 (muR ρ)) := by
  have hf := (Lp.stronglyMeasurable f).measurable.enorm
  have hg := (Lp.stronglyMeasurable g).measurable.enorm
  calc ∫⁻ x, ‖bformF Γ χ R f g x‖ₑ ∂((muR ρ).prod (muR ρ))
      ≤ ∫⁻ x, cntB Γ R x.1 x.2 * ‖g x.1‖ₑ * ‖f x.2‖ₑ ∂((muR ρ).prod (muR ρ)) := by
        refine lintegral_mono fun x => ?_
        unfold bformF
        rw [enorm_mul, enorm_mul, RCLike.enorm_conj, RCLike.enorm_conj, mul_comm (‖f x.2‖ₑ),
          ← mul_assoc]
        gcongr
        exact enorm_bker_le hχ R x.1 x.2
    _ = ∫⁻ p, ∫⁻ q, cntB Γ R p q * ‖g p‖ₑ * ‖f q‖ₑ ∂(muR ρ) ∂(muR ρ) :=
        lintegral_prod _ (((measurable_cntB Γ R).mul (hg.comp measurable_fst)).mul
          (hf.comp measurable_snd)).aemeasurable
    _ ≤ VB R * ((∫⁻ p, ‖g p‖ₑ ^ 2 ∂(muR ρ)) ^ (1 / 2 : ℝ) *
          (∫⁻ q, ‖f q‖ₑ ^ 2 ∂(muR ρ)) ^ (1 / 2 : ℝ)) := lintegral_cntB_mul_le hρ R hg hf
    _ = VB R * (eLpNorm g 2 (muR ρ) * eLpNorm f 2 (muR ρ)) := by
        rw [lintegral_enorm_sq_rpow, lintegral_enorm_sq_rpow]

theorem integrable_bformF {ρ : ℂ × ℝ → ℝ≥0∞} (hρ : IsPU Γ ρ) (hχ : IsUChar Γ χ) {R : ℝ}
    (hR : 0 ≤ R) (f g : Lp ℂ 2 (muR ρ)) :
    Integrable (bformF Γ χ R f g) ((muR ρ).prod (muR ρ)) := by
  refine ⟨(measurable_bformF Γ χ R f g).aestronglyMeasurable, ?_⟩
  refine lt_of_le_of_lt (lintegral_bformF_le hρ hχ R f g) ?_
  exact ENNReal.mul_lt_top (uhsMeasure_hball_lt_top hR)
    (ENNReal.mul_lt_top (Lp.eLpNorm_lt_top g) (Lp.eLpNorm_lt_top f))

/-- **The form** `B(f, g) = ∫∫conj k(p, q)·conj f(q)·g(p) dν(q) dν(p)`, on the product. -/
def bform (Γ : Subgroup SL(2, 𝓞 K)) (χ : SL(2, 𝓞 K) → ℂ) (R : ℝ) (f g : Lp ℂ 2 (muR ρ)) : ℂ :=
  ∫ x, bformF Γ χ R f g x ∂((muR ρ).prod (muR ρ))

theorem norm_bform_le {ρ : ℂ × ℝ → ℝ≥0∞} (hρ : IsPU Γ ρ) (hχ : IsUChar Γ χ) {R : ℝ}
    (hR : 0 ≤ R) (f g : Lp ℂ 2 (muR ρ)) :
    ‖bform Γ χ R f g‖ ≤ (VB R).toReal * ‖f‖ * ‖g‖ := by
  have h1 := (enorm_integral_le_lintegral_enorm (bformF Γ χ R f g)).trans
    (lintegral_bformF_le hρ hχ R f g)
  have hfin : VB R * (eLpNorm g 2 (muR ρ) * eLpNorm f 2 (muR ρ)) ≠ ⊤ :=
    (ENNReal.mul_lt_top (uhsMeasure_hball_lt_top hR)
      (ENNReal.mul_lt_top (Lp.eLpNorm_lt_top g) (Lp.eLpNorm_lt_top f))).ne
  have h2 := ENNReal.toReal_mono hfin h1
  rw [toReal_enorm, ENNReal.toReal_mul, ENNReal.toReal_mul] at h2
  rw [Lp.norm_def, Lp.norm_def]
  unfold bform
  linarith [h2]

end Form

/-! ### Linearity -/

section Linear

variable {ρ : ℂ × ℝ → ℝ≥0∞}

theorem ae_snd_add (f₁ f₂ : Lp ℂ 2 (muR ρ)) :
    ∀ᵐ x ∂((muR ρ).prod (muR ρ)), (f₁ + f₂ : Lp ℂ 2 (muR ρ)) x.2 = f₁ x.2 + f₂ x.2 :=
  Measure.quasiMeasurePreserving_snd.ae_eq_comp (Lp.coeFn_add f₁ f₂)

theorem ae_fst_add (g₁ g₂ : Lp ℂ 2 (muR ρ)) :
    ∀ᵐ x ∂((muR ρ).prod (muR ρ)), (g₁ + g₂ : Lp ℂ 2 (muR ρ)) x.1 = g₁ x.1 + g₂ x.1 :=
  Measure.quasiMeasurePreserving_fst.ae_eq_comp (Lp.coeFn_add g₁ g₂)

theorem ae_snd_smul (c : ℂ) (f : Lp ℂ 2 (muR ρ)) :
    ∀ᵐ x ∂((muR ρ).prod (muR ρ)), (c • f : Lp ℂ 2 (muR ρ)) x.2 = c * f x.2 :=
  Measure.quasiMeasurePreserving_snd.ae_eq_comp (Lp.coeFn_smul c f)

theorem ae_fst_smul (c : ℂ) (g : Lp ℂ 2 (muR ρ)) :
    ∀ᵐ x ∂((muR ρ).prod (muR ρ)), (c • g : Lp ℂ 2 (muR ρ)) x.1 = c * g x.1 :=
  Measure.quasiMeasurePreserving_fst.ae_eq_comp (Lp.coeFn_smul c g)

variable (hρ : IsPU Γ ρ) (hχ : IsUChar Γ χ) {R : ℝ} (hR : 0 ≤ R)
include hρ hχ hR

theorem bform_add_left (f₁ f₂ g : Lp ℂ 2 (muR ρ)) :
    bform Γ χ R (f₁ + f₂) g = bform Γ χ R f₁ g + bform Γ χ R f₂ g := by
  unfold bform
  rw [← integral_add (integrable_bformF hρ hχ hR f₁ g) (integrable_bformF hρ hχ hR f₂ g)]
  refine integral_congr_ae ?_
  filter_upwards [ae_snd_add f₁ f₂] with x hx
  simp only [bformF, hx, map_add]
  ring

omit hρ hχ hR in
theorem bform_smul_left (c : ℂ) (f g : Lp ℂ 2 (muR ρ)) :
    bform Γ χ R (c • f) g = (starRingEnd ℂ) c • bform Γ χ R f g := by
  unfold bform
  rw [smul_eq_mul, ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [ae_snd_smul c f] with x hx
  simp only [bformF, hx, map_mul]
  ring

theorem bform_add_right (f g₁ g₂ : Lp ℂ 2 (muR ρ)) :
    bform Γ χ R f (g₁ + g₂) = bform Γ χ R f g₁ + bform Γ χ R f g₂ := by
  unfold bform
  rw [← integral_add (integrable_bformF hρ hχ hR f g₁) (integrable_bformF hρ hχ hR f g₂)]
  refine integral_congr_ae ?_
  filter_upwards [ae_fst_add g₁ g₂] with x hx
  simp only [bformF, hx]
  ring

omit hρ hχ hR in
theorem bform_smul_right (c : ℂ) (f g : Lp ℂ 2 (muR ρ)) :
    bform Γ χ R f (c • g) = (RingHom.id ℂ) c • bform Γ χ R f g := by
  unfold bform
  rw [RingHom.id_apply, smul_eq_mul, ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [ae_fst_smul c g] with x hx
  simp only [bformF, hx]
  ring

/-- The form as a bounded sesquilinear map. -/
def bformCLM : Lp ℂ 2 (muR ρ) →L⋆[ℂ] Lp ℂ 2 (muR ρ) →L[ℂ] ℂ :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (bform Γ χ R)
      (bform_add_left hρ hχ hR) bform_smul_left (bform_add_right hρ hχ hR) bform_smul_right)
    (VB R).toReal (norm_bform_le hρ hχ hR)

/-- **The ball operator** on `L²(ρ dμ)`: `⟪Kf, g⟫ = B(f, g)` (Mathlib's
`InnerProductSpace.continuousLinearMapOfBilin`). -/
def ballOp : Lp ℂ 2 (muR ρ) →L[ℂ] Lp ℂ 2 (muR ρ) :=
  InnerProductSpace.continuousLinearMapOfBilin (bformCLM hρ hχ hR)

theorem inner_ballOp (f g : Lp ℂ 2 (muR ρ)) :
    ⟪ballOp hρ hχ hR f, g⟫_ℂ = bform Γ χ R f g := by
  rw [ballOp, InnerProductSpace.continuousLinearMapOfBilin_apply]
  rfl

end Linear

/-! ### Self-adjointness -/

section SelfAdjoint

variable {ρ : ℂ × ℝ → ℝ≥0∞}

theorem ae_prod_UHS : ∀ᵐ x ∂((muR ρ).prod (muR ρ)), x.1 ∈ UHS ∧ x.2 ∈ UHS :=
  (Measure.quasiMeasurePreserving_fst.ae (ae_muR_UHS ρ)).and
    (Measure.quasiMeasurePreserving_snd.ae (ae_muR_UHS ρ))

/-- **The form is Hermitian**: `B(f, g) = conj B(g, f)`, by swapping the two coordinates of the
product and `bker_swap`. -/
theorem bform_eq_conj (hχ : IsUChar Γ χ) (R : ℝ) (f g : Lp ℂ 2 (muR ρ)) :
    bform Γ χ R f g = conj (bform Γ χ R g f) := by
  unfold bform
  rw [← integral_conj]
  have e := integral_prod_swap (μ := muR ρ) (ν := muR ρ)
    (fun x => conj (bformF Γ χ R g f x))
  rw [← e]
  refine integral_congr_ae ?_
  filter_upwards [ae_prod_UHS] with x hx
  simp only [bformF, Prod.fst_swap, Prod.snd_swap, map_mul, Complex.conj_conj]
  rw [bker_swap hχ R hx.1 hx.2]
  ring

/-- **The ball operator is self-adjoint**. -/
theorem isSelfAdjoint_ballOp (hρ : IsPU Γ ρ) (hχ : IsUChar Γ χ) {R : ℝ} (hR : 0 ≤ R) :
    IsSelfAdjoint (ballOp hρ hχ hR) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff']
  refine ((ContinuousLinearMap.eq_adjoint_iff _ _).2 fun f g => ?_).symm
  rw [inner_ballOp, ← inner_conj_symm, inner_ballOp]
  exact bform_eq_conj hχ R f g

end SelfAdjoint

end Eis

end

#print axioms Eis.IsUChar.map_one
#print axioms Eis.IsUChar.map_inv
#print axioms Eis.measurable_hball_indC
#print axioms Eis.measurable_bker
#print axioms Eis.enorm_bker_le
#print axioms Eis.bker_swap
#print axioms Eis.lintegral_enorm_sq_rpow
#print axioms Eis.measurable_bformF
#print axioms Eis.lintegral_bformF_le
#print axioms Eis.integrable_bformF
#print axioms Eis.norm_bform_le
#print axioms Eis.ae_snd_add
#print axioms Eis.ae_fst_add
#print axioms Eis.ae_snd_smul
#print axioms Eis.ae_fst_smul
#print axioms Eis.bform_add_left
#print axioms Eis.bform_smul_left
#print axioms Eis.bform_add_right
#print axioms Eis.bform_smul_right
#print axioms Eis.inner_ballOp
#print axioms Eis.ae_prod_UHS
#print axioms Eis.bform_eq_conj
#print axioms Eis.isSelfAdjoint_ballOp
