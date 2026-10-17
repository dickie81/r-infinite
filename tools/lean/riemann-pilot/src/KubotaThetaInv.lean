import KubotaThetaZero

/-! # θ is invariant under `SL_2(ℤ)` (round 443)

S5f-12 of round 360's plan, part 4. Round 442's next step planned θ's invariance under `S` and `T` through
round 439's `translates_eq_zero` on `Γ_1(3)` itself, a translation lemma on `3P` from round 435's chart onto
the torus, and the passage to θ's continuous Fourier series (round 436's `thS`). This round proves the three,
for `r > 0`, `Y > 0` and θ's representative `θ̃` (round 425's `thetaF`):

* **The trace from `Γ_1(3)` to itself** (**`trK_self`**, with `subsingleton_quot_gam3`): the identity at every
  point of upper half-space on functions automorphic on `Γ_1(3)` with `κ`, since there is one coset and
  `|κ| = 1`.
* **The principle for one translate** (**`thetaF_comp_ae_eq`** and **`thetaF_toSL_ae`**, with `conjGam3`, a
  definition, and `actP_map_inv`): for `g` of determinant `1` with `e : Γ_1(3) ≃ Γ_1(3)`,
  `e(γ)·(g·p) = g·(γ·p)` and `κ(e(γ)) = κ(γ)`, if the constant terms at `∞` of `θ̃∘g − θ̃` and of
  `θ̃ − θ̃∘g⁻¹` vanish for almost every `v > 0`, then `θ̃∘g = θ̃` almost everywhere (round 439's
  `translates_eq_zero` with `H = H′_i = Γ_1(3)`, the translates `g` and `I`, and the coefficients `1` and
  `−1`). Conjugation by `h ∈ SL_2(ℤ)` is such an `e` (round 382's `gam3_normal` and `kub_conj_toSL`).
* **`S`** (**`thetaF_sS_ae`**, with `actP_neg`, `slAct_sS_inv` and `const_theta_ne_zero`): `θ̃∘S = θ̃` almost
  everywhere. `S⁻¹ = −S` acts as `S`, and rounds 433 and 442 give `θ̃` and `θ̃∘S` the same constant term
  `(9√3/2)·Res φ·v^{2/3}` at `∞`; it is nonzero (round 417's `phiRes_ne_zero`), so both slices are integrable
  on `3P` (Mathlib's `Integrable.of_integral_ne_zero`).
* **Translation, and `T`** (**`integral_fundP3_add`** and **`thetaF_sT_ae`**, with `tch_add`, `tch_lift`,
  `toSL_T_eq`, `slAct_sT` and `slAct_sT_inv`): `∫_{3P} f(z + c) dz = ∫_{3P} f(z) dz` for `f` periodic under
  `3ℤ[ω]` and every `c ∈ ℂ`, by Mathlib's `integral_preimage` on the unit torus at the offsets `0` and `a`
  with `tch(a) = c`. With round 437's `thetaF_add_period` this gives `θ̃∘T = θ̃` almost everywhere,
  `T = (1, 1; 0, 1)`.
* **At every point** (**`thS_slAct_of_ae`**, **`thS_slAct_toSL`**, **`isAut_thS_Gam2`**, **`atG_thS_int`** and
  **`exists_theta_series_inv`**, with `restrict_UHS_ac`, `map_toSL_σO` and `atG_thS_toSL`):
  `thS(h·p) = thS(p)` for every `h ∈ SL_2(ℤ)` and every `p` in upper half-space, by continuity as in round
  437's `isAut_thS` and Mathlib's `SpecialLinearGroup.SL2Z_generators`; `thS` is automorphic on
  `Γ_2 = SL_2(ℤ)Γ_1(3)` with round 382's extension `κ₂` of `κ`; and with round 437's three clauses
  (`exists_theta_series`) this gives four clauses of round 361's `KubotaTheta` for `thS`.
-/

open MeasureTheory Set Filter NumberField Complex UnitAddTorus
open scoped ENNReal Topology MatrixGroups ComplexConjugate

noncomputable section

namespace Eis

/-! ### The trace to `Γ_1(3)` from `Γ_1(3)` itself -/

/-- `Γ_1(3)` has one coset in itself. -/
theorem subsingleton_quot_gam3 : Subsingleton (Gam3 ⧸ Gam3.subgroupOf Gam3) := by
  refine ⟨fun a b => ?_⟩
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
  exact QuotientGroup.eq.2 (Subgroup.mem_subgroupOf.2 (a⁻¹ * b).2)

/-- **The trace from `Γ_1(3)` to itself is the identity** on functions automorphic on `Γ_1(3)` with `κ`, at
every point of upper half-space: there is one coset, and `|κ| = 1` there. -/
theorem trK_self {f : ℂ × ℝ → ℂ} (hf : IsAut Gam3 (fun g => kub ↑g) f) {p : ℂ × ℝ} (hp : p ∈ UHS) :
    trK Gam3 f p = f p := by
  have := subsingleton_quot_gam3
  unfold trK
  set q₀ : Gam3 ⧸ Gam3.subgroupOf Gam3 := QuotientGroup.mk 1
  rw [tsum_eq_single q₀ fun b hb => absurd (Subsingleton.elim b q₀) hb]
  have hq : ((q₀.out : Gam3) : SL(2, 𝓞 K))⁻¹ ∈ Gam3 := Gam3.inv_mem q₀.out.2
  have h := hf _ hq p hp
  simp only at h
  rw [h, ← mul_assoc, mul_comm (conj _), kub_mul_conj_kub hq, one_mul]

/-! ### The principle for one translate -/

/-- **The constant-term principle for one translate on `Γ_1(3)`**: for `g` of determinant `1` with
`e : Γ_1(3) ≃ Γ_1(3)`, `e(γ)·(g·p) = g·(γ·p)` and `κ(e(γ)) = κ(γ)`, if the constant terms at `∞` of
`θ̃∘g − θ̃` and of `θ̃ − θ̃∘g⁻¹` vanish for almost every `v > 0`, then `θ̃∘g = θ̃` almost everywhere (round
439's `translates_eq_zero`, with `H = H′ = Γ_1(3)`). -/
theorem thetaF_comp_ae_eq {r : ℝ} (hr : 0 < r) {Y : ℝ} (hY : 0 < Y) {g : Matrix (Fin 2) (Fin 2) ℂ}
    (hg : g.det = 1) (e : Gam3 ≃ Gam3)
    (he : ∀ γ : Gam3, ∀ p ∈ UHS, slAct (e γ) (actP g p) = actP g (slAct γ p))
    (hκ : ∀ γ : Gam3, kub ↑(e γ : SL(2, 𝓞 K)) = kub ↑(γ : SL(2, 𝓞 K)))
    (h1 : ∀ᵐ v ∂(volume.restrict (Ioi (0 : ℝ))),
      ∫ z in fundP3, (thetaF r Y hY (actP g (z, v)) - thetaF r Y hY (z, v)) = 0)
    (h2 : ∀ᵐ v ∂(volume.restrict (Ioi (0 : ℝ))),
      ∫ z in fundP3, (thetaF r Y hY (z, v) - thetaF r Y hY (actP g⁻¹ (z, v))) = 0) :
    ∀ᵐ p ∂uhsMeasure, thetaF r Y hY (actP g p) = thetaF r Y hY p := by
  have := subsingleton_quot_gam3
  have : Finite (Gam3 ⧸ Gam3.subgroupOf Gam3) := Finite.of_subsingleton
  have hgs : ∀ i, (![g, 1] i).det = 1 := by
    intro i
    fin_cases i
    · exact hg
    · simp
  have hes : ∀ i, ∀ γ : Gam3, ∀ p ∈ UHS,
      slAct (![e, Equiv.refl Gam3] i γ) (actP (![g, 1] i) p) = actP (![g, 1] i) (slAct γ p) := by
    intro i
    fin_cases i
    · exact he
    · intro γ p _
      simp [actP_one]
  have hκs : ∀ i, ∀ γ : Gam3,
      kub ↑(![e, Equiv.refl Gam3] i γ : SL(2, 𝓞 K)) = kub ↑(γ : SL(2, 𝓞 K)) := by
    intro i
    fin_cases i
    · exact hκ
    · intro γ
      rfl
  have hθaut := isAut_thetaF r Y hY
  have hDaut : IsAut Gam3 (fun g => kub ↑g)
      fun p => ∑ j, ![(1 : ℂ), -1] j * thetaF r Y hY (actP (![g, 1] j) p) := by
    intro γ hγ p hp
    simp only
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have h := isAut_comp_actP (hgs j) (![e, Equiv.refl Gam3] j) (hes j) (hκs j) hθaut γ hγ p hp
    simp only at h
    rw [h]
    ring
  have h0 : ∀ i, ∀ᵐ v ∂(volume.restrict (Ioi (0 : ℝ))), ∫ z in fundP3,
      trK Gam3 (fun p => ∑ j, ![(1 : ℂ), -1] j *
        thetaF r Y hY (actP (![g, 1] j) (actP (![g, 1] i)⁻¹ p))) (z, v) = 0 := by
    intro i
    have hFaut := isAut_comp_actP_inv (hgs i) (![e, Equiv.refl Gam3] i) (hes i) (hκs i) hDaut
    have key : ∀ v : ℝ, 0 < v → ∫ z in fundP3,
        trK Gam3 (fun p => ∑ j, ![(1 : ℂ), -1] j *
          thetaF r Y hY (actP (![g, 1] j) (actP (![g, 1] i)⁻¹ p))) (z, v) =
        ∫ z in fundP3, ∑ j, ![(1 : ℂ), -1] j *
          thetaF r Y hY (actP (![g, 1] j) (actP (![g, 1] i)⁻¹ (z, v))) := by
      intro v hv
      refine integral_congr_ae (Eventually.of_forall fun z => ?_)
      exact trK_self hFaut (show (z, v) ∈ UHS from hv)
    fin_cases i
    · filter_upwards [h2, ae_restrict_mem measurableSet_Ioi] with v hv hv0
      rw [key v hv0, ← hv]
      refine integral_congr_ae (Eventually.of_forall fun z => ?_)
      simp [Fin.sum_univ_two, actP_actP_inv hg (show (z, v) ∈ UHS from hv0), actP_one, sub_eq_add_neg]
    · filter_upwards [h1, ae_restrict_mem measurableSet_Ioi] with v hv hv0
      rw [key v hv0, ← hv]
      refine integral_congr_ae (Eventually.of_forall fun z => ?_)
      simp [Fin.sum_univ_two, actP_one, sub_eq_add_neg]
  have h := translates_eq_zero hr hY (H := Gam3) le_rfl ![g, 1] hgs (fun _ => Gam3) (fun _ => le_rfl)
    ![e, Equiv.refl Gam3] hes hκs ![(1 : ℂ), -1] h0
  filter_upwards [h] with p hp
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, one_mul,
    actP_one, neg_one_mul] at hp
  exact sub_eq_zero.1 (by rw [sub_eq_add_neg]; exact hp)

/-! ### Conjugation by `SL_2(ℤ)` -/

/-- Conjugation by `g ∈ SL_2(ℤ[ω])`, as a permutation of `Γ_1(3)` (round 382's `gam3_normal`). -/
def conjGam3 (g : SL(2, 𝓞 K)) : Gam3 ≃ Gam3 where
  toFun γ := ⟨g * γ * g⁻¹, gam3_normal.conj_mem _ γ.2 g⟩
  invFun γ := ⟨g⁻¹ * γ * g, by simpa using gam3_normal.conj_mem _ γ.2 g⁻¹⟩
  left_inv γ := Subtype.ext (by simp [mul_assoc])
  right_inv γ := Subtype.ext (by simp [mul_assoc])

/-- The inverse of the complex matrix of `γ` acts as `γ⁻¹` on upper half-space. -/
theorem actP_map_inv (γ : SL(2, 𝓞 K)) {p : ℂ × ℝ} (hp : p ∈ UHS) :
    actP ((γ : Matrix (Fin 2) (Fin 2) (𝓞 K)).map σO)⁻¹ p = slAct γ⁻¹ p := by
  conv_lhs => rw [← slAct_slAct_inv γ hp]
  exact actP_inv_actP (det_map_σO γ.2) (slAct_mem _ hp)

/-- **The principle for `h ∈ SL_2(ℤ)`**: if the constant terms at `∞` of `θ̃∘h − θ̃` and of `θ̃ − θ̃∘h⁻¹`
vanish for almost every `v > 0`, then `θ̃∘h = θ̃` almost everywhere (`thetaF_comp_ae_eq` with conjugation by
`h`, which preserves `κ` by round 382's `kub_conj_toSL`). -/
theorem thetaF_toSL_ae {r : ℝ} (hr : 0 < r) {Y : ℝ} (hY : 0 < Y) (h : SL(2, ℤ))
    (h1 : ∀ᵐ v ∂(volume.restrict (Ioi (0 : ℝ))),
      ∫ z in fundP3, (thetaF r Y hY (slAct (toSL h) (z, v)) - thetaF r Y hY (z, v)) = 0)
    (h2 : ∀ᵐ v ∂(volume.restrict (Ioi (0 : ℝ))),
      ∫ z in fundP3, (thetaF r Y hY (z, v) - thetaF r Y hY (slAct (toSL h)⁻¹ (z, v))) = 0) :
    ∀ᵐ p ∂uhsMeasure, thetaF r Y hY (slAct (toSL h) p) = thetaF r Y hY p := by
  have hκ : ∀ γ : Gam3, kub ↑(conjGam3 (toSL h) γ : SL(2, 𝓞 K)) = kub ↑(γ : SL(2, 𝓞 K)) := by
    intro γ
    have h' := kub_conj_toSL h⁻¹ γ.2
    rw [map_inv, inv_inv] at h'
    exact h'
  refine thetaF_comp_ae_eq hr hY (det_map_σO (toSL h).2) (conjGam3 (toSL h))
    (fun γ p hp => (slAct_conj (toSL h) γ hp).symm) hκ h1 ?_
  filter_upwards [h2, ae_restrict_mem measurableSet_Ioi] with v hv hv0
  rw [← hv]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only
  rw [actP_map_inv _ (show (z, v) ∈ UHS from hv0)]

/-! ### `S` -/

/-- **`−g` acts as `g`**. -/
theorem actP_neg (g : Matrix (Fin 2) (Fin 2) ℂ) (p : ℂ × ℝ) : actP (-g) p = actP g p := by
  have h1 : ∀ a b : ℂ, -a * p.1 + -b = -(a * p.1 + b) := fun a b => by ring
  simp only [actP, uhsAct, uhsZ, uhsV, uhsDen, Matrix.neg_apply, h1, Complex.normSq_neg, map_neg,
    neg_mul_neg]

/-- **`S⁻¹ = −S` acts as `S`**. -/
theorem slAct_sS_inv (p : ℂ × ℝ) : slAct sS⁻¹ p = slAct sS p := by
  have e : ((sS⁻¹ : SL(2, 𝓞 K)) : Matrix (Fin 2) (Fin 2) (𝓞 K)).map σO =
      -((sS : Matrix (Fin 2) (Fin 2) (𝓞 K)).map σO) := by
    rw [Matrix.SpecialLinearGroup.coe_inv, sS_coe, Matrix.adjugate_fin_two_of]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  unfold slAct
  rw [e, actP_neg]

/-- `(9√3/2)·Res φ·v^{2/3} ≠ 0` for `v > 0` (round 417's `phiRes_ne_zero`). -/
theorem const_theta_ne_zero {v : ℝ} (hv : 0 < v) :
    ((9 * (Real.sqrt 3 / 2) : ℝ) : ℂ) * (phiG (4 / 3) / 3) * ((v ^ (2 / 3 : ℝ) : ℝ) : ℂ) ≠ 0 := by
  refine mul_ne_zero (mul_ne_zero nine_sqrt_ne_zero phiRes_ne_zero) ?_
  exact_mod_cast (Real.rpow_pos_of_pos hv _).ne'

/-- **`θ̃∘S = θ̃` almost everywhere**: by rounds 433 and 442 the constant terms at `∞` of `θ̃` and of `θ̃∘S`
are both `(9√3/2)·Res φ·v^{2/3}`, and `S⁻¹` acts as `S`. -/
theorem thetaF_sS_ae {r : ℝ} (hr : 0 < r) {Y : ℝ} (hY : 0 < Y) :
    ∀ᵐ p ∂uhsMeasure, thetaF r Y hY (slAct sS p) = thetaF r Y hY p := by
  have key : ∀ᵐ v ∂(volume.restrict (Ioi (0 : ℝ))),
      ∫ z in fundP3, (thetaF r Y hY (slAct sS (z, v)) - thetaF r Y hY (z, v)) = 0 := by
    filter_upwards [const_thetaF_ae hr hY, const_thetaFS_ae hr hY, ae_restrict_mem measurableSet_Ioi]
      with v h0 hS hv
    have hi0 : Integrable (fun z => thetaF r Y hY (z, v)) (volume.restrict fundP3) :=
      Integrable.of_integral_ne_zero (by rw [h0]; exact const_theta_ne_zero hv)
    have hiS : Integrable (fun z => thetaFS r Y hY (z, v)) (volume.restrict fundP3) :=
      Integrable.of_integral_ne_zero (by rw [hS]; exact const_theta_ne_zero hv)
    have e := integral_sub hiS hi0
    simp only [thetaFS] at e hS
    rw [e, hS, h0, sub_self]
  refine thetaF_toSL_ae hr hY ModularGroup.S key ?_
  filter_upwards [key] with v hv
  have e : ∀ z : ℂ, thetaF r Y hY (z, v) - thetaF r Y hY (slAct (toSL ModularGroup.S)⁻¹ (z, v)) =
      -(thetaF r Y hY (slAct sS (z, v)) - thetaF r Y hY (z, v)) := fun z => by
    rw [show (toSL ModularGroup.S)⁻¹ = sS⁻¹ from rfl, slAct_sS_inv]
    ring
  simp_rw [e]
  rw [integral_neg, hv, neg_zero]

/-! ### Translation on `ℂ/3ℤ[ω]`, and `T` -/

/-- The chart is additive. -/
theorem tch_add (y a : Fin 2 → ℝ) : tch (y + a) = tch y + tch a := by
  simp only [tch_apply, Pi.add_apply]
  push_cast
  ring

/-- **The chart's lift**: for `f` periodic under `3ℤ[ω]`, `f(tch(y′)) = f(tch(y))` for the representative `y′`
of `y` modulo `ℤ²` in `(0, 1]²`. -/
theorem tch_lift {f : ℂ → ℂ} (hper : ∀ z u, f (z + σO (3 * u)) = f z) (y : Fin 2 → ℝ) :
    f (tch (measurableEquivPiIoc 0 (fun i => (y i : UnitAddCircle))).1) = f (tch y) := by
  obtain ⟨n, hn⟩ : ∃ n : Fin 2 → ℤ,
      (measurableEquivPiIoc 0 (fun i => (y i : UnitAddCircle))).1 = fun i => y i - (n i : ℝ) := by
    refine ⟨fun i => toIocDiv (zero_lt_one' ℝ) 0 (y i), funext fun i => ?_⟩
    show toIocMod (zero_lt_one' ℝ) 0 (y i) = y i - ((toIocDiv (zero_lt_one' ℝ) 0 (y i) : ℤ) : ℝ)
    rw [← self_sub_toIocDiv_zsmul, Int.smul_one_eq_cast]
  have ht : tch (fun i => y i - (n i : ℝ)) = tch y + σO (3 * -crd n) := by
    rw [mul_neg, map_neg, σO_three_mul]
    simp only [tch_apply, crd, map_add, map_mul, map_intCast, σO_ω]
    push_cast
    ring
  rw [hn, ht, hper]

/-- **Translation on `ℂ/3ℤ[ω]`**: `∫_{3P} f(z + c) dz = ∫_{3P} f(z) dz` for `f` periodic under `3ℤ[ω]` and
every `c ∈ ℂ`, through round 435's chart and Mathlib's `integral_preimage` on the torus at two offsets. -/
theorem integral_fundP3_add {f : ℂ → ℂ} (hper : ∀ z u, f (z + σO (3 * u)) = f z) (c : ℂ) :
    ∫ z in fundP3, f (z + c) = ∫ z in fundP3, f z := by
  obtain ⟨a, rfl⟩ : ∃ a : Fin 2 → ℝ, tch a = c :=
    ⟨tchE.symm c, by rw [← tchE_apply, MeasurableEquiv.apply_symm_apply]⟩
  set G : UnitAddTorus (Fin 2) → ℂ := fun t => f (tch (measurableEquivPiIoc 0 t).1)
  have hGy : ∀ y : Fin 2 → ℝ, G (fun i => (y i : UnitAddCircle)) = f (tch y) := tch_lift hper
  have h0 := integral_preimage (d := Fin 2) G 0
  have ha := integral_preimage (d := Fin 2) G a
  simp only [Pi.zero_apply, zero_add, hGy] at h0 ha
  have hpre : (fun y => y + a) ⁻¹' {y : Fin 2 → ℝ | ∀ i, y i ∈ Ioc (a i) (a i + 1)} =
      {y : Fin 2 → ℝ | ∀ i, y i ∈ Ioc (0 : ℝ) 1} := by
    ext y
    simp only [mem_preimage, mem_ofPred_eq, Pi.add_apply, mem_Ioc]
    refine forall_congr' fun i => ?_
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  have hsh := (measurePreserving_add_right volume a).setIntegral_preimage_emb
    (measurableEmbedding_addRight a) (fun y => f (tch y)) {y : Fin 2 → ℝ | ∀ i, y i ∈ Ioc (a i) (a i + 1)}
  rw [hpre] at hsh
  have hb1 : ∫ y in {y : Fin 2 → ℝ | ∀ i, y i ∈ Ioc (0 : ℝ) 1}, f (tch y + tch a) =
      ((9 * (Real.sqrt 3 / 2))⁻¹ : ℝ) • ∫ z in fundP3, f (z + tch a) :=
    integral_box_tch fun z => f (z + tch a)
  have hb2 := integral_box_tch f
  have e1 : ∫ y in {y : Fin 2 → ℝ | ∀ i, y i ∈ Ioc (0 : ℝ) 1}, f (tch y + tch a) =
      ∫ y in {y : Fin 2 → ℝ | ∀ i, y i ∈ Ioc (0 : ℝ) 1}, f (tch (y + a)) := by
    simp only [tch_add]
  have hk : ((9 * (Real.sqrt 3 / 2))⁻¹ : ℝ) ≠ 0 := by positivity
  refine smul_right_injective ℂ hk ?_
  dsimp only
  rw [← hb1, ← hb2, e1, hsh, ← ha, h0]

/-- `T = (1, 1; 0, 1)` in `SL_2(ℤ[ω])` is round 385's translation by `1`. -/
theorem toSL_T_eq : toSL ModularGroup.T = slT 1 := by
  ext i j
  rw [coe_toSL_T, coe_slT]

/-- `T` acts by `(z, v) ↦ (z + 1, v)`. -/
theorem slAct_sT (p : ℂ × ℝ) : slAct (toSL ModularGroup.T) p = (p.1 + 1, p.2) := by
  rw [toSL_T_eq, slAct_slT, map_one]

/-- `T⁻¹` acts by `(z, v) ↦ (z − 1, v)`. -/
theorem slAct_sT_inv (p : ℂ × ℝ) : slAct (toSL ModularGroup.T)⁻¹ p = (p.1 - 1, p.2) := by
  have e : (toSL ModularGroup.T)⁻¹ = slT (-1) := by
    rw [toSL_T_eq]
    refine inv_eq_of_mul_eq_one_right ?_
    rw [slT_mul_slT, add_neg_cancel, slT_zero]
  rw [e, slAct_slT, map_neg, map_one, sub_eq_add_neg]

/-- **`θ̃∘T = θ̃` almost everywhere**: `θ̃` is periodic under `3ℤ[ω]` (round 437's `thetaF_add_period`), so by
the translation lemma its translates by `±1` have its constant term at `∞`. -/
theorem thetaF_sT_ae {r : ℝ} (hr : 0 < r) {Y : ℝ} (hY : 0 < Y) :
    ∀ᵐ p ∂uhsMeasure, thetaF r Y hY (slAct (toSL ModularGroup.T) p) = thetaF r Y hY p := by
  have key : ∀ c : ℂ, ∀ᵐ v ∂(volume.restrict (Ioi (0 : ℝ))),
      ∫ z in fundP3, (thetaF r Y hY (z + c, v) - thetaF r Y hY (z, v)) = 0 := by
    intro c
    filter_upwards [const_thetaF_ae hr hY, ae_restrict_mem measurableSet_Ioi] with v h0 hv
    have htr : ∫ z in fundP3, thetaF r Y hY (z + c, v) = ∫ z in fundP3, thetaF r Y hY (z, v) :=
      integral_fundP3_add (f := fun z => thetaF r Y hY (z, v)) (fun z u => thetaF_add_period r Y hY z u hv) c
    have hi0 : Integrable (fun z => thetaF r Y hY (z, v)) (volume.restrict fundP3) :=
      Integrable.of_integral_ne_zero (by rw [h0]; exact const_theta_ne_zero hv)
    have hic : Integrable (fun z => thetaF r Y hY (z + c, v)) (volume.restrict fundP3) :=
      Integrable.of_integral_ne_zero (by rw [htr, h0]; exact const_theta_ne_zero hv)
    rw [integral_sub hic hi0, htr, sub_self]
  refine thetaF_toSL_ae hr hY ModularGroup.T ?_ ?_
  · filter_upwards [key 1] with v hv
    simp only [slAct_sT]
    exact hv
  · filter_upwards [key (-1)] with v hv
    have e : ∀ z : ℂ, thetaF r Y hY (z, v) - thetaF r Y hY (slAct (toSL ModularGroup.T)⁻¹ (z, v)) =
        -(thetaF r Y hY (z + -1, v) - thetaF r Y hY (z, v)) := fun z => by
      rw [slAct_sT_inv, ← sub_eq_add_neg]
      ring
    simp_rw [e]
    rw [integral_neg, hv, neg_zero]

/-! ### At every point -/

/-- Lebesgue measure on upper half-space has the null sets of `dz dv/v³` there. -/
theorem restrict_UHS_ac : volume.restrict UHS ≪ uhsMeasure := by
  refine withDensity_absolutelyContinuous' measurable_uhsW.aemeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_UHS] with q hq
  have hq' : (0 : ℝ) < q.2 := hq
  unfold uhsW
  exact (ENNReal.ofReal_pos.2 (zpow_pos hq' _)).ne'

/-- **From `θ̃` to its Fourier series at every point**: if `θ̃∘γ = θ̃` almost everywhere, for
`γ ∈ SL_2(ℤ[ω])`, then `thS(γ·p) = thS(p)` at every point `p` of upper half-space (as round 437's
`isAut_thS`). -/
theorem thS_slAct_of_ae {r : ℝ} (hr : 0 < r) {Y : ℝ} (hY : 0 < Y) (γ : SL(2, 𝓞 K))
    (h : ∀ᵐ p ∂uhsMeasure, thetaF r Y hY (slAct γ p) = thetaF r Y hY p) {p : ℂ × ℝ} (hp : p ∈ UHS) :
    thS r Y hY (slAct γ p) = thS r Y hY p := by
  classical
  obtain ⟨S', hS'⟩ : ∃ S' : ℂ × ℝ → ℂ, S' = UHS.piecewise (thS r Y hY) 0 := ⟨_, rfl⟩
  have hS'm : Measurable S' := by
    rw [hS']
    exact (continuousOn_thS hr hY).measurable_piecewise continuousOn_const measurableSet_UHS
  have hset : MeasurableSet {q : ℂ × ℝ | thetaF r Y hY q = S' q} :=
    measurableSet_eq_fun (measurable_thetaF r Y hY) hS'm
  have hS'ae : ∀ᵐ q ∂(volume.restrict UHS), q ∈ {q : ℂ × ℝ | thetaF r Y hY q = S' q} := by
    filter_upwards [ae_thetaF_eq_thS hr hY, ae_restrict_mem measurableSet_UHS] with q hq hqU
    show thetaF r Y hY q = S' q
    rw [hS', Set.piecewise_eq_of_mem _ _ _ hqU]
    exact hq
  have hae : ∀ᵐ q ∂(volume.restrict UHS), thS r Y hY (slAct γ q) = thS r Y hY q := by
    filter_upwards [hS'ae, ae_slAct hset hS'ae γ, ae_restrict_mem measurableSet_UHS,
      restrict_UHS_ac.ae_le h] with q hq1 hq2 hqU hq3
    have hq1' : thetaF r Y hY q = thS r Y hY q := by
      have := hq1
      simp only [hS', Set.piecewise_eq_of_mem _ _ _ hqU] at this
      exact this
    have hq2' : thetaF r Y hY (slAct γ q) = thS r Y hY (slAct γ q) := by
      have := hq2
      simp only [hS', Set.piecewise_eq_of_mem _ _ _ (slAct_mem γ hqU)] at this
      exact this
    rw [← hq2', hq3, hq1']
  have hU : IsOpen UHS := isOpen_lt continuous_const continuous_snd
  have hc1 : ContinuousOn (fun q => thS r Y hY (slAct γ q)) UHS :=
    (continuousOn_thS hr hY).comp (continuousOn_slAct γ) fun q hq => slAct_mem γ hq
  exact Measure.eqOn_open_of_ae_eq hae hU hc1 (continuousOn_thS hr hY) hp

/-- **θ's Fourier series is invariant under `SL_2(ℤ)`**: `thS(h·p) = thS(p)` for `h ∈ SL_2(ℤ)` and every `p`
in upper half-space, since `S` and `T` generate `SL_2(ℤ)` (Mathlib's `SpecialLinearGroup.SL2Z_generators`). -/
theorem thS_slAct_toSL {r : ℝ} (hr : 0 < r) {Y : ℝ} (hY : 0 < Y) (h : SL(2, ℤ)) {p : ℂ × ℝ}
    (hp : p ∈ UHS) : thS r Y hY (slAct (toSL h) p) = thS r Y hY p := by
  have hall : h ∈ Subgroup.closure {ModularGroup.S, ModularGroup.T} := by
    rw [SpecialLinearGroup.SL2Z_generators]; exact Subgroup.mem_top h
  induction hall using Subgroup.closure_induction generalizing p with
  | mem x hx =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact thS_slAct_of_ae hr hY _ (thetaF_sS_ae hr hY) hp
    · exact thS_slAct_of_ae hr hY _ (thetaF_sT_ae hr hY) hp
  | one => rw [map_one, slAct_one]
  | mul x y _ _ ihx ihy => rw [map_mul, slAct_mul _ _ hp, ihx (slAct_mem _ hp), ihy hp]
  | inv x _ ih =>
    have h1 := ih (slAct_mem (toSL x)⁻¹ hp)
    rw [slAct_slAct_inv _ hp] at h1
    rw [map_inv]
    exact h1.symm

/-- **θ's Fourier series is automorphic on `Γ_2 = SL_2(ℤ)Γ_1(3)`** with round 382's extension `κ₂` of Kubota's
character: `thS(g·p) = κ₂(g)·thS(p)` for `g ∈ Γ_2` and every `p` in upper half-space. -/
theorem isAut_thS_Gam2 {r : ℝ} (hr : 0 < r) {Y : ℝ} (hY : 0 < Y) : IsAut Gam2 kub2 (thS r Y hY) := by
  intro g hg p hp
  obtain ⟨h, hh⟩ := mem_Gam2.1 hg
  have e : slAct g p = slAct (toSL h) (slAct ((toSL h)⁻¹ * g) p) := by
    rw [← slAct_mul _ _ hp, mul_inv_cancel_left]
  rw [e, thS_slAct_toSL hr hY h (slAct_mem _ hp), isAut_thS hr hY _ hh p hp, kub2_eq h hh]

/-- The complex matrix of `toSL g` is the integer matrix of `g`, cast to `ℂ`. -/
theorem map_toSL_σO (g : SL(2, ℤ)) :
    ((toSL g : SL(2, 𝓞 K)) : Matrix (Fin 2) (Fin 2) (𝓞 K)).map σO =
      (g : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℂ) := by
  rw [coe_toSL]
  ext i j
  simp

/-- **Invariance under `SL_2(ℤ)` in round 361's notation `atG`**, for `g ∈ SL_2(ℤ)`. -/
theorem atG_thS_toSL {r : ℝ} (hr : 0 < r) {Y : ℝ} (hY : 0 < Y) (g : SL(2, ℤ)) (z : ℂ) {v : ℝ}
    (hv : 0 < v) :
    atG (fun z v => thS r Y hY (z, v)) (((toSL g : SL(2, 𝓞 K)) : Matrix (Fin 2) (Fin 2) (𝓞 K)).map σO)
      z v = thS r Y hY (z, v) := by
  have h := thS_slAct_toSL hr hY g (show (z, v) ∈ UHS from hv)
  exact h

/-- **The `SL_2(ℤ)` clause of round 361's `KubotaTheta`** for θ's Fourier series:
`thS(γ(z + vj)) = thS(z + vj)` for an integer matrix `γ` of determinant `1` and `v > 0`, in round 361's
notation `atG`. -/
theorem atG_thS_int {r : ℝ} (hr : 0 < r) {Y : ℝ} (hY : 0 < Y) (γ : Matrix (Fin 2) (Fin 2) ℤ)
    (hdet : γ.det = 1) (z : ℂ) {v : ℝ} (hv : 0 < v) :
    atG (fun z v => thS r Y hY (z, v)) (γ.map (Int.castRingHom ℂ)) z v = thS r Y hY (z, v) := by
  have e : γ.map (Int.castRingHom ℂ) =
      ((toSL ⟨γ, hdet⟩ : SL(2, 𝓞 K)) : Matrix (Fin 2) (Fin 2) (𝓞 K)).map σO :=
    (map_toSL_σO ⟨γ, hdet⟩).symm
  have h := atG_thS_toSL hr hY ⟨γ, hdet⟩ z hv
  exact (congrArg (fun M => atG (fun z v => thS r Y hY (z, v)) M z v) e).trans h

/-- **Four clauses of round 361's `KubotaTheta`**, for θ's Fourier series: round 437's three
(`exists_theta_series`) and invariance under `SL_2(ℤ)`. -/
theorem exists_theta_series_inv {r : ℝ} (hr : 0 < r) {Y : ℝ} (hY : 0 < Y) :
    ∃ (θ : ℂ → ℝ → ℂ) (c₀ : ℂ) (τ : 𝓞 K → ℂ),
      (∀ z v, 0 < v → θ z v = thSer c₀ τ z v) ∧ (∀ m, τ m ≠ 0 → δ3 ∣ m) ∧
      (∀ γ : Matrix (Fin 2) (Fin 2) ℤ, γ.det = 1 → ∀ z v, 0 < v →
        atG θ (γ.map (Int.castRingHom ℂ)) z v = θ z v) ∧
      (∀ γ : Matrix (Fin 2) (Fin 2) (𝓞 K), γ.det = 1 → ModThree γ → ∀ z v, 0 < v →
        atG θ (γ.map σO) z v = kub γ * θ z v) ∧
      ∀ᵐ p ∂(volume.restrict UHS), thetaF r Y hY p = θ p.1 p.2 :=
  ⟨fun z v => thS r Y hY (z, v), phiG (4 / 3) / 3, tauTh r Y hY, fun _ _ _ => rfl,
    fun _ h => dvd_of_tauTh_ne_zero h, fun γ hdet z _ hv => atG_thS_int hr hY γ hdet z hv,
    fun γ hdet h3 z _ hv => atG_thS hr hY γ hdet h3 z hv, ae_thetaF_eq_thS hr hY⟩

end Eis

end

#print axioms Eis.subsingleton_quot_gam3
#print axioms Eis.trK_self
#print axioms Eis.thetaF_comp_ae_eq
#print axioms Eis.actP_map_inv
#print axioms Eis.thetaF_toSL_ae
#print axioms Eis.actP_neg
#print axioms Eis.slAct_sS_inv
#print axioms Eis.const_theta_ne_zero
#print axioms Eis.thetaF_sS_ae
#print axioms Eis.tch_add
#print axioms Eis.tch_lift
#print axioms Eis.integral_fundP3_add
#print axioms Eis.toSL_T_eq
#print axioms Eis.slAct_sT
#print axioms Eis.slAct_sT_inv
#print axioms Eis.thetaF_sT_ae
#print axioms Eis.restrict_UHS_ac
#print axioms Eis.thS_slAct_of_ae
#print axioms Eis.thS_slAct_toSL
#print axioms Eis.isAut_thS_Gam2
#print axioms Eis.map_toSL_σO
#print axioms Eis.atG_thS_toSL
#print axioms Eis.atG_thS_int
#print axioms Eis.exists_theta_series_inv
