import KubotaResidue

/-! # Unfolding pseudo-Eisenstein series (round 426)

S5f-10 of round 360's plan, part 9 (S5f-10e, second part). Round 425's next step planned the pairing of `ũ_s`
with a pseudo-Eisenstein series `E(ψ)` through unfolding over `Γ_∞\Γ_1(3)` in complex form. This round proves
the unfolding: for `u` automorphic with Kubota's character,
`∫conj E(ψ)·u dν = ∫_{3P×(0,∞)} conj ψ(v)·u(z, v) dz dv/v³`, with `ν = ρ_G dμ` as in round 423 and `3P` round
389's period parallelogram of `3ℤ[ω]`.

* **Unfolding over a family** (**`lintegral_unfold_family`** and **`integral_unfold_family`**): for elements
  `g_i` of `SL_2(ℤ[ω])` with `Σ_i ρ(g_i⁻¹·q) = ρ′(q)` on upper half-space, `∫ρ(p)·Σ_i F(g_i·p) dμ = ∫ρ′F dμ`,
  and in complex form `∫Σ_i Ψ(g_i·p) dν_ρ(p) = ∫Ψ dν_{ρ′}` when `∫ρ′|Ψ| dμ < ∞` (round 386's
  `lintegral_slAct`, round 383's `integral_actP` and Mathlib's `integral_tsum`, as in round 422's
  `kfun_eq_bavg`).
* **`Γ_1(3)` as translations times bottom rows** (`BRowT`, `gamRow` and `decGam3`, definitions;
  **`eq_slT_of_Gam3`**, with `gamRow_mem`, `gamRow_10`, `gamRow_11`, `slT_mul_10`, `slT_mul_11`,
  `slT_mul_slT`, `slT_inv` and `decGam3_apply`): an element of `Γ_1(3)` with bottom row `(0, 1)` is a
  translation `T_{3t}`, so `(t, (c, d)) ↦ T_{3t}·γ_{(c, d)}` is a bijection from `ℤ[ω] × (bottom rows)` onto
  `Γ_1(3)`, with `γ_{(c, d)}` chosen by round 387's `exists_Gam3_of_BRow`.
* **Partitions of unity for the translations** (`rhoH` and `rhoT3`, definitions; **`tsum_rhoH`**,
  **`lintegral_rhoH_eq`** and **`integral_rhoH_eq`**, with `measurable_rhoH`, `measurable_rhoT3`,
  `rhoT3_le_one`, `kub_slT`, `rhoH_le_one` and `tsum_rhoT3`): `ρ_H(p) = Σ_{(c,d)} ρ_G(γ_{(c,d)}⁻¹·p)` and
  `ρ_3(z, v) = 1_{3P}(z)` both sum to `1` over the translations by `3ℤ[ω]` (round 386's `IsPU.tsum_inv`, round
  389's `tsum_fundP3`). For `Φ` periodic under `3ℤ[ω]` with `∫ρ_3|Φ| dμ < ∞`, `∫Φ dν_{ρ_H} = ∫Φ dν_{ρ_3}`.
* **The pairing** (**`integral_conj_pseis_mul`** and **`inner_toLp_pseis`**, with `muR_rhoT3`,
  `conj_psTerm_mul` and `conj_pseis_mul`): `κ(γ) = conj (c/d)₃` (round 387's `kub_eq_conj_cub`) turns
  `conj E(ψ)·u` into `Σ_{(c,d)} conj ψ(v(γ_{(c,d)}p))·u(γ_{(c,d)}p)`, and the two unfoldings give
  `∫conj E(ψ)·u dν = ∫_{3P×(0,∞)} conj ψ(v)·u(z, v) dz dv/v³` for `ψ` and `u` measurable with the right side
  absolutely convergent; in `L²(ν)` this is `⟨E(ψ), u⟩`.
-/

open MeasureTheory Set Filter NumberField Complex Ideal
open scoped ENNReal Topology MatrixGroups ComplexConjugate

noncomputable section

namespace Eis

/-! ### Unfolding over a family -/

/-- **Unfolding over a family, in `[0, ∞]`**: `∫ρ(p)·Σ_i F(g_i·p) dμ = ∫ρ′F dμ` when
`Σ_i ρ(g_i⁻¹·q) = ρ′(q)` on upper half-space. -/
theorem lintegral_unfold_family {ι : Type*} [Countable ι] (g : ι → SL(2, 𝓞 K))
    {ρ ρ' : ℂ × ℝ → ℝ≥0∞} (hρ : Measurable ρ) (hsum : ∀ q ∈ UHS, ∑' i, ρ (slAct (g i)⁻¹ q) = ρ' q)
    {F : ℂ × ℝ → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ p, ρ p * ∑' i, F (slAct (g i) p) ∂uhsMeasure = ∫⁻ q, ρ' q * F q ∂uhsMeasure := by
  have h1 : ∀ i, ∫⁻ p, ρ p * F (slAct (g i) p) ∂uhsMeasure =
      ∫⁻ q, ρ (slAct (g i)⁻¹ q) * F q ∂uhsMeasure := by
    intro i
    rw [← lintegral_slAct (g i)⁻¹ (F := fun p => ρ p * F (slAct (g i) p))
      (hρ.mul (hF.comp (measurable_slAct _)))]
    refine lintegral_congr_ae ?_
    filter_upwards [ae_UHS] with q hq
    rw [slAct_slAct_inv _ hq]
  calc ∫⁻ p, ρ p * ∑' i, F (slAct (g i) p) ∂uhsMeasure
      = ∫⁻ p, ∑' i, ρ p * F (slAct (g i) p) ∂uhsMeasure := by simp_rw [ENNReal.tsum_mul_left]
    _ = ∑' i, ∫⁻ p, ρ p * F (slAct (g i) p) ∂uhsMeasure :=
        lintegral_tsum fun i => (hρ.mul (hF.comp (measurable_slAct _))).aemeasurable
    _ = ∑' i, ∫⁻ q, ρ (slAct (g i)⁻¹ q) * F q ∂uhsMeasure := tsum_congr h1
    _ = ∫⁻ q, ∑' i, ρ (slAct (g i)⁻¹ q) * F q ∂uhsMeasure :=
        (lintegral_tsum fun i => ((hρ.comp (measurable_slAct _)).mul hF).aemeasurable).symm
    _ = ∫⁻ q, ρ' q * F q ∂uhsMeasure := by
        refine lintegral_congr_ae ?_
        filter_upwards [ae_UHS] with q hq
        rw [ENNReal.tsum_mul_right, hsum q hq]

/-- **Unfolding over a family, in complex form**: `∫Σ_i Ψ(g_i·p) dν_ρ(p) = ∫Ψ dν_{ρ′}` when
`Σ_i ρ(g_i⁻¹·q) = ρ′(q) < ∞` on upper half-space, `ρ < ∞` there, and `∫ρ′|Ψ| dμ < ∞`. -/
theorem integral_unfold_family {ι : Type*} [Countable ι] (g : ι → SL(2, 𝓞 K))
    {ρ ρ' : ℂ × ℝ → ℝ≥0∞} (hρ : Measurable ρ) (hρ' : Measurable ρ')
    (hsum : ∀ q ∈ UHS, ∑' i, ρ (slAct (g i)⁻¹ q) = ρ' q) (hρfin : ∀ q ∈ UHS, ρ q < ⊤)
    (hρ'fin : ∀ q ∈ UHS, ρ' q < ⊤) {Ψ : ℂ × ℝ → ℂ} (hΨ : Measurable Ψ)
    (hfin : ∫⁻ q, ρ' q * ‖Ψ q‖ₑ ∂uhsMeasure ≠ ⊤) :
    ∫ p, ∑' i, Ψ (slAct (g i) p) ∂(muR ρ) = ∫ q, Ψ q ∂(muR ρ') := by
  have hρae : ∀ᵐ q ∂uhsMeasure, ρ q < ⊤ := by
    filter_upwards [ae_UHS] with q hq
    exact hρfin q hq
  have hρ'ae : ∀ᵐ q ∂uhsMeasure, ρ' q < ⊤ := by
    filter_upwards [ae_UHS] with q hq
    exact hρ'fin q hq
  -- the first exchange
  have hA : ∑' i, ∫⁻ p, ‖Ψ (slAct (g i) p)‖ₑ ∂(muR ρ) ≠ ⊤ := by
    have e : ∀ i, ∫⁻ p, ‖Ψ (slAct (g i) p)‖ₑ ∂(muR ρ) =
        ∫⁻ p, ρ p * ‖Ψ (slAct (g i) p)‖ₑ ∂uhsMeasure := fun i => by
      have hm1 : Measurable fun p => ‖Ψ (slAct (g i) p)‖ₑ := (hΨ.comp (measurable_slAct _)).enorm
      rw [muR, lintegral_withDensity_eq_lintegral_mul _ hρ hm1]
      rfl
    simp_rw [e]
    have hm : ∀ i, AEMeasurable (fun p => ρ p * ‖Ψ (slAct (g i) p)‖ₑ) uhsMeasure :=
      fun i => (hρ.mul (hΨ.comp (measurable_slAct _)).enorm).aemeasurable
    rw [← lintegral_tsum hm]
    simp_rw [ENNReal.tsum_mul_left]
    have hu := lintegral_unfold_family g hρ hsum (F := fun q => ‖Ψ q‖ₑ) hΨ.enorm
    rw [hu]
    exact hfin
  have hAm : ∀ i, AEStronglyMeasurable (fun p => Ψ (slAct (g i) p)) (muR ρ) :=
    fun i => (hΨ.comp (measurable_slAct _)).aestronglyMeasurable
  rw [integral_tsum hAm hA]
  -- each term
  have h3 : ∀ i, ∫ p, Ψ (slAct (g i) p) ∂(muR ρ) =
      ∫ q, (ρ (slAct (g i)⁻¹ q)).toReal • Ψ q ∂uhsMeasure := by
    intro i
    rw [muR, integral_withDensity_eq_integral_toReal_smul hρ hρae]
    have hH : AEStronglyMeasurable (fun q => (ρ q).toReal • Ψ (slAct (g i) q)) uhsMeasure :=
      (hρ.ennreal_toReal.smul (hΨ.comp (measurable_slAct _))).aestronglyMeasurable
    rw [← integral_actP (det_map_σO (g i)⁻¹.2) hH]
    refine integral_congr_ae ?_
    filter_upwards [ae_UHS] with q hq
    change (ρ (slAct (g i)⁻¹ q)).toReal • Ψ (slAct (g i) (slAct (g i)⁻¹ q)) = _
    rw [slAct_slAct_inv _ hq]
  simp_rw [h3]
  -- the second exchange
  have hB : ∑' i, ∫⁻ q, ‖(ρ (slAct (g i)⁻¹ q)).toReal • Ψ q‖ₑ ∂uhsMeasure ≠ ⊤ := by
    refine ne_top_of_le_ne_top (b := ∑' i, ∫⁻ q, ρ (slAct (g i)⁻¹ q) * ‖Ψ q‖ₑ ∂uhsMeasure) ?_
      (ENNReal.tsum_le_tsum fun i => lintegral_mono fun q => ?_)
    · have hm : ∀ i, AEMeasurable (fun q => ρ (slAct (g i)⁻¹ q) * ‖Ψ q‖ₑ) uhsMeasure :=
        fun i => ((hρ.comp (measurable_slAct _)).mul hΨ.enorm).aemeasurable
      rw [← lintegral_tsum hm]
      have e : ∫⁻ q, ∑' i, ρ (slAct (g i)⁻¹ q) * ‖Ψ q‖ₑ ∂uhsMeasure =
          ∫⁻ q, ρ' q * ‖Ψ q‖ₑ ∂uhsMeasure := by
        refine lintegral_congr_ae ?_
        filter_upwards [ae_UHS] with q hq
        rw [ENNReal.tsum_mul_right, hsum q hq]
      rw [e]
      exact hfin
    · rw [enorm_smul, Real.enorm_of_nonneg ENNReal.toReal_nonneg]
      gcongr
      exact ENNReal.ofReal_toReal_le
  have hBm : ∀ i, AEStronglyMeasurable (fun q => (ρ (slAct (g i)⁻¹ q)).toReal • Ψ q) uhsMeasure :=
    fun i => ((hρ.comp (measurable_slAct _)).ennreal_toReal.smul hΨ).aestronglyMeasurable
  rw [← integral_tsum hBm hB, muR, integral_withDensity_eq_integral_toReal_smul hρ' hρ'ae]
  refine integral_congr_ae ?_
  filter_upwards [ae_UHS] with q hq
  have hfin_i : ∀ i, ρ (slAct (g i)⁻¹ q) ≠ ⊤ := fun i =>
    ne_top_of_le_ne_top (hρ'fin q hq).ne
      (by rw [← hsum q hq]; exact ENNReal.le_tsum (f := fun j => ρ (slAct (g j)⁻¹ q)) i)
  rw [(ENNReal.summable_toReal (f := fun j => ρ (slAct (g j)⁻¹ q))
      (by rw [hsum q hq]; exact (hρ'fin q hq).ne)).tsum_smul_const,
    ← ENNReal.tsum_toReal_eq hfin_i, hsum q hq]

/-! ### `Γ_1(3)` as translations times bottom rows -/

/-- The bottom rows of `Γ_1(3)`, as a type. -/
abbrev BRowT := {cd : 𝓞 K × 𝓞 K // BRow cd}

/-- An element of `Γ_1(3)` with bottom row `(c, d)` (round 387's `exists_Gam3_of_BRow`). -/
def gamRow (cd : BRowT) : SL(2, 𝓞 K) := Classical.choose (exists_Gam3_of_BRow cd.2)

theorem gamRow_mem (cd : BRowT) : gamRow cd ∈ Gam3 :=
  (Classical.choose_spec (exists_Gam3_of_BRow cd.2)).1

theorem gamRow_10 (cd : BRowT) : gamRow cd 1 0 = cd.1.1 :=
  (Classical.choose_spec (exists_Gam3_of_BRow cd.2)).2.1

theorem gamRow_11 (cd : BRowT) : gamRow cd 1 1 = cd.1.2 :=
  (Classical.choose_spec (exists_Gam3_of_BRow cd.2)).2.2

theorem slT_mul_10 (t : 𝓞 K) (γ : SL(2, 𝓞 K)) : (slT t * γ) 1 0 = γ 1 0 := by
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_slT, Matrix.mul_apply, Fin.sum_univ_two]
  simp

theorem slT_mul_11 (t : 𝓞 K) (γ : SL(2, 𝓞 K)) : (slT t * γ) 1 1 = γ 1 1 := by
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_slT, Matrix.mul_apply, Fin.sum_univ_two]
  simp

theorem slT_mul_slT (s t : 𝓞 K) : slT s * slT t = slT (s + t) := by
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_slT, coe_slT, coe_slT]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem slT_inv (t : 𝓞 K) : (slT t)⁻¹ = slT (-t) := by
  rw [eq_comm, ← mul_eq_one_iff_eq_inv, slT_mul_slT, neg_add_cancel, slT_zero]

/-- **An element of `Γ_1(3)` with bottom row `(0, 1)` is a translation by `3ℤ[ω]`.** -/
theorem eq_slT_of_Gam3 {γ : SL(2, 𝓞 K)} (hγ : γ ∈ Gam3) (h0 : γ 1 0 = 0) (h1 : γ 1 1 = 1) :
    ∃ t : 𝓞 K, γ = slT (3 * t) := by
  have h3 := mem_Gam3.1 hγ
  have hdet := γ.2
  obtain ⟨a, b, c, d, hγe⟩ := exists_fin_two_eq (γ : Matrix (Fin 2) (Fin 2) (𝓞 K))
  have e10 : γ 1 0 = c := by rw [show γ 1 0 = (γ : Matrix (Fin 2) (Fin 2) (𝓞 K)) 1 0 from rfl, hγe]; rfl
  have e11 : γ 1 1 = d := by rw [show γ 1 1 = (γ : Matrix (Fin 2) (Fin 2) (𝓞 K)) 1 1 from rfl, hγe]; rfl
  rw [e10] at h0
  rw [e11] at h1
  rw [hγe, modThree_iff] at h3
  rw [hγe, Matrix.det_fin_two_of, h0, h1, mul_one, mul_zero, sub_zero] at hdet
  obtain ⟨t, ht⟩ := h3.2.1
  refine ⟨t, ?_⟩
  ext i j
  have e : (γ : Matrix (Fin 2) (Fin 2) (𝓞 K)) = !![1, 3 * t; 0, 1] := by
    rw [hγe, hdet, ht, h0, h1]
  rw [e, coe_slT]

/-- **`Γ_1(3) ≅ 3ℤ[ω] × (bottom rows)`**: `(t, (c, d)) ↦ T_{3t}·γ_{(c, d)}`. -/
def decGam3 : 𝓞 K × BRowT ≃ Gam3 :=
  Equiv.ofBijective (fun x => ⟨slT (3 * x.1) * gamRow x.2,
      Gam3.mul_mem (slT_mem_Gam3 (dvd_mul_right 3 x.1)) (gamRow_mem x.2)⟩)
    ⟨fun x y hxy => by
      have h := congrArg Subtype.val hxy
      simp only at h
      have hcd : x.2 = y.2 := by
        have h10 := congrArg (fun γ : SL(2, 𝓞 K) => γ 1 0) h
        have h11 := congrArg (fun γ : SL(2, 𝓞 K) => γ 1 1) h
        simp only [slT_mul_10, slT_mul_11, gamRow_10, gamRow_11] at h10 h11
        exact Subtype.ext (Prod.ext h10 h11)
      rw [hcd] at h
      have h2 := mul_right_cancel h
      have h01 := congrArg (fun γ : SL(2, 𝓞 K) => γ 0 1) h2
      simp only [slT] at h01
      change (!![1, 3 * x.1; 0, 1] : Matrix (Fin 2) (Fin 2) (𝓞 K)) 0 1 =
        (!![1, 3 * y.1; 0, 1] : Matrix (Fin 2) (Fin 2) (𝓞 K)) 0 1 at h01
      simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.empty_val', Matrix.cons_val_fin_one] at h01
      exact Prod.ext (mul_left_cancel₀ (by norm_num) h01) hcd,
    fun γ => by
      set cd : BRowT := ⟨(γ.1 1 0, γ.1 1 1), bRow_of_Gam3 γ.2⟩
      have hδ : (γ : SL(2, 𝓞 K)) * (gamRow cd)⁻¹ ∈ Gam3 :=
        Gam3.mul_mem γ.2 (Gam3.inv_mem (gamRow_mem cd))
      have hrow : rowMul (gamRow cd)⁻¹ ((γ : SL(2, 𝓞 K)) 1 0, (γ : SL(2, 𝓞 K)) 1 1) =
          (((γ : SL(2, 𝓞 K)) * (gamRow cd)⁻¹) 1 0, ((γ : SL(2, 𝓞 K)) * (gamRow cd)⁻¹) 1 1) :=
        rowMul_bottom _ _
      have hrow' : rowMul (gamRow cd)⁻¹ ((gamRow cd) 1 0, (gamRow cd) 1 1) = (0, 1) := by
        rw [rowMul_bottom, mul_inv_cancel]
        simp
      have he : ((γ : SL(2, 𝓞 K)) 1 0, (γ : SL(2, 𝓞 K)) 1 1) = ((gamRow cd) 1 0, (gamRow cd) 1 1) := by
        rw [gamRow_10, gamRow_11]
      rw [he, hrow'] at hrow
      obtain ⟨t, ht⟩ := eq_slT_of_Gam3 hδ (congrArg Prod.fst hrow).symm (congrArg Prod.snd hrow).symm
      refine ⟨(t, cd), Subtype.ext ?_⟩
      change slT (3 * t) * gamRow cd = (γ : SL(2, 𝓞 K))
      rw [← ht, inv_mul_cancel_right]⟩

theorem decGam3_apply (x : 𝓞 K × BRowT) :
    (decGam3 x : SL(2, 𝓞 K)) = slT (3 * x.1) * gamRow x.2 := rfl

/-! ### Partitions of unity for the translations -/

/-- `ρ_H(p) = Σ_{(c,d)} ρ_G(γ_{(c,d)}⁻¹·p)`, from round 423's partition of unity `ρ_G` for `Γ_1(3)`. -/
def rhoH (p : ℂ × ℝ) : ℝ≥0∞ := ∑' cd : BRowT, rhoG (slAct (gamRow cd)⁻¹ p)

/-- `ρ_3(z, v) = 1_{3P}(z)`, with `3P` round 389's period parallelogram of `3ℤ[ω]`. -/
def rhoT3 (p : ℂ × ℝ) : ℝ≥0∞ := fundP3.indicator 1 p.1

theorem measurable_rhoH : Measurable rhoH :=
  Measurable.tsum fun _ => isPU_rhoG.1.comp (measurable_slAct _)

theorem measurable_rhoT3 : Measurable rhoT3 :=
  (measurable_one.indicator measurableSet_fundP3).comp measurable_fst

theorem rhoT3_le_one (p : ℂ × ℝ) : rhoT3 p ≤ 1 := by
  unfold rhoT3
  by_cases h : p.1 ∈ fundP3
  · rw [indicator_of_mem h]; rfl
  · rw [indicator_of_notMem h]; exact zero_le

theorem kub_slT (t : 𝓞 K) : kub ↑(slT t) = 1 := by
  rw [coe_slT]
  unfold kub
  simp

/-- **`ρ_H` is a partition of unity for the translations**: `Σ_t ρ_H(T_{3t}·p) = 1`, by
`Γ_1(3) ≅ 3ℤ[ω] × (bottom rows)` and round 386's `IsPU.tsum_inv`. -/
theorem tsum_rhoH {p : ℂ × ℝ} (hp : p ∈ UHS) :
    ∑' t : 𝓞 K, rhoH (slAct (slT (3 * t)) p) = 1 := by
  unfold rhoH
  rw [← ENNReal.tsum_prod]
  have e : ∀ x : 𝓞 K × BRowT, rhoG (slAct (gamRow x.2)⁻¹ (slAct (slT (3 * x.1)) p)) =
      rhoG (slAct (((decGam3 (-x.1, x.2) : Gam3) : SL(2, 𝓞 K)))⁻¹ p) := by
    intro x
    rw [decGam3_apply, mul_inv_rev, slT_inv, slAct_mul _ _ hp, mul_neg, neg_neg]
  rw [tsum_congr e]
  have h := (((Equiv.neg (𝓞 K)).prodCongr (Equiv.refl BRowT)).trans decGam3).tsum_eq
    (fun γ : Gam3 => rhoG (slAct (γ : SL(2, 𝓞 K))⁻¹ p))
  simp only [Equiv.trans_apply, Equiv.prodCongr_apply, Equiv.neg_apply, Equiv.coe_refl] at h
  rw [show (∑' b : 𝓞 K × BRowT, rhoG (slAct (((decGam3 (-b.1, b.2) : Gam3) : SL(2, 𝓞 K)))⁻¹ p)) =
      ∑' c : 𝓞 K × BRowT, rhoG (slAct (((decGam3 (Prod.map Neg.neg id c) : Gam3) :
        SL(2, 𝓞 K)))⁻¹ p) from rfl, h]
  have h2 := isPU_rhoG.tsum_inv hp
  simp only [Subgroup.coe_inv] at h2
  exact h2

theorem rhoH_le_one {p : ℂ × ℝ} (hp : p ∈ UHS) : rhoH p ≤ 1 := by
  have h := tsum_rhoH hp
  have h0 : rhoH (slAct (slT (3 * 0)) p) ≤ ∑' t : 𝓞 K, rhoH (slAct (slT (3 * t)) p) :=
    ENNReal.le_tsum (f := fun t : 𝓞 K => rhoH (slAct (slT (3 * t)) p)) 0
  rwa [mul_zero, slT_zero, slAct_one, h] at h0

/-- `Σ_t ρ_3(T_{3t}⁻¹·p) = 1` (round 389's `tsum_fundP3`). -/
theorem tsum_rhoT3 (p : ℂ × ℝ) : ∑' t : 𝓞 K, rhoT3 (slAct (slT (3 * t))⁻¹ p) = 1 := by
  unfold rhoT3
  have e : ∀ t : 𝓞 K, (slAct (slT (3 * t))⁻¹ p).1 = p.1 + σO (3 * -t) := by
    intro t
    rw [slT_inv, slAct_slT, mul_neg]
  simp_rw [e]
  have h := (Equiv.neg (𝓞 K)).tsum_eq (fun t => fundP3.indicator (1 : ℂ → ℝ≥0∞) (p.1 + σO (3 * t)))
  simp only [Equiv.neg_apply] at h
  rw [h, tsum_fundP3]

/-- **Changing the partition of unity for the translations, in `[0, ∞]`**: `∫ρ_H F = ∫ρ_3 F` for `F` periodic
under `3ℤ[ω]`. -/
theorem lintegral_rhoH_eq {F : ℂ × ℝ → ℝ≥0∞} (hF : Measurable F)
    (hper : ∀ t : 𝓞 K, ∀ p ∈ UHS, F (slAct (slT (3 * t)) p) = F p) :
    ∫⁻ p, rhoH p * F p ∂uhsMeasure = ∫⁻ p, rhoT3 p * F p ∂uhsMeasure := by
  have h := lintegral_unfold_family (fun t : 𝓞 K => slT (3 * t)) measurable_rhoT3
    (fun q _ => tsum_rhoT3 q) (F := fun p => rhoH p * F p) (measurable_rhoH.mul hF)
  simp only [one_mul] at h
  rw [← h]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_UHS] with p hp
  congr 1
  simp_rw [hper _ p hp]
  rw [ENNReal.tsum_mul_right, tsum_rhoH hp, one_mul]

/-- **Changing the partition of unity for the translations**: `∫Φ dν_{ρ_H} = ∫Φ dν_{ρ_3}` for `Φ` periodic
under `3ℤ[ω]` with `∫ρ_3|Φ| dμ < ∞`. -/
theorem integral_rhoH_eq {Φ : ℂ × ℝ → ℂ} (hΦ : Measurable Φ)
    (hper : ∀ t : 𝓞 K, ∀ p ∈ UHS, Φ (slAct (slT (3 * t)) p) = Φ p)
    (hfin : ∫⁻ p, rhoT3 p * ‖Φ p‖ₑ ∂uhsMeasure ≠ ⊤) :
    ∫ p, Φ p ∂(muR rhoH) = ∫ p, Φ p ∂(muR rhoT3) := by
  have hfinH : ∫⁻ p, rhoH p * ‖Φ p‖ₑ ∂uhsMeasure ≠ ⊤ := by
    rw [lintegral_rhoH_eq hΦ.enorm fun t p hp => by rw [hper t p hp]]
    exact hfin
  set Ψ : ℂ × ℝ → ℂ := fun p => (rhoH p).toReal • Φ p with hΨ
  have hΨm : Measurable Ψ := measurable_rhoH.ennreal_toReal.smul hΦ
  have hΨfin : ∫⁻ q, (1 : ℂ × ℝ → ℝ≥0∞) q * ‖Ψ q‖ₑ ∂uhsMeasure ≠ ⊤ := by
    refine ne_top_of_le_ne_top hfinH (lintegral_mono fun q => ?_)
    simp only [Pi.one_apply, one_mul, hΨ, enorm_smul, Real.enorm_of_nonneg ENNReal.toReal_nonneg]
    gcongr
    exact ENNReal.ofReal_toReal_le
  have h := integral_unfold_family (fun t : 𝓞 K => slT (3 * t)) measurable_rhoT3 measurable_const
    (fun q _ => tsum_rhoT3 q) (fun q _ => lt_of_le_of_lt (rhoT3_le_one q) ENNReal.one_lt_top)
    (fun q _ => ENNReal.one_lt_top) hΨm hΨfin
  have hm1 : muR (fun _ : ℂ × ℝ => (1 : ℝ≥0∞)) = uhsMeasure := withDensity_one
  rw [hm1] at h
  rw [muR, integral_withDensity_eq_integral_toReal_smul measurable_rhoH
    (by filter_upwards [ae_UHS] with q hq; exact lt_of_le_of_lt (rhoH_le_one hq) ENNReal.one_lt_top)]
  rw [← h]
  refine integral_congr_ae ?_
  have hae : ∀ᵐ p ∂(muR rhoT3), p ∈ UHS := ae_muR_UHS rhoT3
  filter_upwards [hae] with p hp
  simp only [hΨ]
  simp_rw [hper _ p hp]
  have hfin_t : ∀ t : 𝓞 K, rhoH (slAct (slT (3 * t)) p) ≠ ⊤ := fun t =>
    (lt_of_le_of_lt (rhoH_le_one (slAct_mem _ hp)) ENNReal.one_lt_top).ne
  rw [(ENNReal.summable_toReal (f := fun t : 𝓞 K => rhoH (slAct (slT (3 * t)) p))
      (by rw [tsum_rhoH hp]; exact ENNReal.one_ne_top)).tsum_smul_const,
    ← ENNReal.tsum_toReal_eq hfin_t, tsum_rhoH hp, ENNReal.toReal_one, one_smul]

/-! ### The pairing with a pseudo-Eisenstein series -/

/-- `ν_{ρ_3}` is `dz dv/v³` on `3P × (0, ∞)`. -/
theorem muR_rhoT3 : muR rhoT3 = uhsMeasure.restrict (Prod.fst ⁻¹' fundP3) := by
  have e : rhoT3 = (Prod.fst ⁻¹' fundP3).indicator 1 := by
    funext p
    unfold rhoT3
    by_cases h : p.1 ∈ fundP3
    · rw [indicator_of_mem h, indicator_of_mem (show p ∈ Prod.fst ⁻¹' fundP3 from h)]; rfl
    · rw [indicator_of_notMem h, indicator_of_notMem (show p ∉ Prod.fst ⁻¹' fundP3 from h)]
  rw [muR, e, withDensity_indicator_one (measurableSet_fundP3.preimage measurable_fst)]

/-- **The terms of `conj E(ψ)·u`**: for `u` automorphic with Kubota's character,
`conj((c/d)₃·ψ(v(γp)))·u(p) = conj ψ(v(γp))·u(γp)` with `γ = γ_{(c,d)}`, since `κ(γ) = conj (c/d)₃` (round
387's `kub_eq_conj_cub`). -/
theorem conj_psTerm_mul {u : ℂ × ℝ → ℂ} (hu : IsAut Gam3 (fun g => kub ↑g) u) (ψ : ℝ → ℂ)
    {p : ℂ × ℝ} (hp : p ∈ UHS) (cd : BRowT) :
    conj (psTerm ψ p cd.1) * u p =
      conj (ψ (slAct (gamRow cd) p).2) * u (slAct (gamRow cd) p) := by
  rw [psTerm_eq_of_row cd.2 (gamRow_10 cd) (gamRow_11 cd), hu _ (gamRow_mem cd) p hp]
  dsimp only
  rw [kub_eq_conj_cub (gamRow cd).2 (mem_Gam3.1 (gamRow_mem cd))]
  rw [gamRow_10, gamRow_11, map_mul]
  ring

/-- **`conj E(ψ)·u` as a sum over the bottom rows**: `Σ_{(c,d)} conj ψ(v(γ_{(c,d)}p))·u(γ_{(c,d)}p)`. -/
theorem conj_pseis_mul {u : ℂ × ℝ → ℂ} (hu : IsAut Gam3 (fun g => kub ↑g) u) (ψ : ℝ → ℂ)
    {p : ℂ × ℝ} (hp : p ∈ UHS) :
    conj (pseis ψ p) * u p =
      ∑' cd : BRowT, conj (ψ (slAct (gamRow cd) p).2) * u (slAct (gamRow cd) p) := by
  have hsupp : Function.support (psTerm ψ p) ⊆ {cd | BRow cd} := fun cd h => by
    by_contra hb
    exact h (psTerm_of_not_bRow ψ p hb)
  unfold pseis
  rw [← tsum_subtype_eq_of_support_subset hsupp, Complex.conj_tsum, ← tsum_mul_right]
  exact tsum_congr fun cd => conj_psTerm_mul hu ψ hp cd

/-- **Unfolding a pseudo-Eisenstein series against an automorphic function**: for `ψ` and `u` measurable, `u`
automorphic with Kubota's character, and `∫_{3P×(0,∞)} |ψ(v)u(z, v)| dz dv/v³ < ∞`,
`∫conj E(ψ)·u dν = ∫_{3P×(0,∞)} conj ψ(v)·u(z, v) dz dv/v³`. -/
theorem integral_conj_pseis_mul {ψ : ℝ → ℂ} (hψ : Measurable ψ) {u : ℂ × ℝ → ℂ}
    (hu : IsAut Gam3 (fun g => kub ↑g) u) (hum : Measurable u)
    (hfin : ∫⁻ p, rhoT3 p * ‖conj (ψ p.2) * u p‖ₑ ∂uhsMeasure ≠ ⊤) :
    ∫ p, conj (pseis ψ p) * u p ∂(muR rhoG) =
      ∫ p in Prod.fst ⁻¹' fundP3, conj (ψ p.2) * u p ∂uhsMeasure := by
  set Φ : ℂ × ℝ → ℂ := fun p => conj (ψ p.2) * u p with hΦ
  have hΦm : Measurable Φ :=
    (Complex.continuous_conj.measurable.comp (hψ.comp measurable_snd)).mul hum
  have hper : ∀ t : 𝓞 K, ∀ p ∈ UHS, Φ (slAct (slT (3 * t)) p) = Φ p := by
    intro t p hp
    simp only [hΦ]
    rw [hu _ (slT_mem_Gam3 (dvd_mul_right 3 t)) p hp]
    dsimp only
    rw [kub_slT, one_mul, slAct_slT]
  have hfinH : ∫⁻ q, rhoH q * ‖Φ q‖ₑ ∂uhsMeasure ≠ ⊤ := by
    rw [lintegral_rhoH_eq hΦm.enorm fun t p hp => by rw [hper t p hp]]
    exact hfin
  have h1 : ∫ p, conj (pseis ψ p) * u p ∂(muR rhoG) =
      ∫ p, ∑' cd : BRowT, Φ (slAct (gamRow cd) p) ∂(muR rhoG) := by
    refine integral_congr_ae ?_
    filter_upwards [ae_muR_UHS rhoG] with p hp
    exact conj_pseis_mul hu ψ hp
  rw [h1, integral_unfold_family gamRow isPU_rhoG.1 measurable_rhoH (fun q _ => rfl)
    (fun q hq => lt_of_le_of_lt (isPU_rhoG.le_one hq) ENNReal.one_lt_top)
    (fun q hq => lt_of_le_of_lt (rhoH_le_one hq) ENNReal.one_lt_top) hΦm hfinH,
    integral_rhoH_eq hΦm hper hfin, muR_rhoT3]

/-- **The pairing in `L²(ν)`**: `⟨E(ψ), u⟩ = ∫_{3P×(0,∞)} conj ψ(v)·u(z, v) dz dv/v³`. -/
theorem inner_toLp_pseis {ψ : ℝ → ℂ} (hψ : Measurable ψ) (hψ2 : MemLp (pseis ψ) 2 (muR rhoG))
    {u : ℂ × ℝ → ℂ} (hu : IsAut Gam3 (fun g => kub ↑g) u) (hum : Measurable u)
    (hu2 : MemLp u 2 (muR rhoG))
    (hfin : ∫⁻ p, rhoT3 p * ‖conj (ψ p.2) * u p‖ₑ ∂uhsMeasure ≠ ⊤) :
    inner ℂ (hψ2.toLp (pseis ψ)) (hu2.toLp u) =
      ∫ p in Prod.fst ⁻¹' fundP3, conj (ψ p.2) * u p ∂uhsMeasure := by
  rw [L2.inner_def, ← integral_conj_pseis_mul hψ hu hum hfin]
  refine integral_congr_ae ?_
  filter_upwards [hψ2.coeFn_toLp, hu2.coeFn_toLp] with p h1 h2
  rw [RCLike.inner_apply', h1, h2]

end Eis

end

#print axioms Eis.lintegral_unfold_family
#print axioms Eis.integral_unfold_family
#print axioms Eis.gamRow_mem
#print axioms Eis.gamRow_10
#print axioms Eis.gamRow_11
#print axioms Eis.slT_mul_10
#print axioms Eis.slT_mul_11
#print axioms Eis.slT_mul_slT
#print axioms Eis.slT_inv
#print axioms Eis.eq_slT_of_Gam3
#print axioms Eis.decGam3_apply
#print axioms Eis.measurable_rhoH
#print axioms Eis.measurable_rhoT3
#print axioms Eis.rhoT3_le_one
#print axioms Eis.kub_slT
#print axioms Eis.tsum_rhoH
#print axioms Eis.rhoH_le_one
#print axioms Eis.tsum_rhoT3
#print axioms Eis.lintegral_rhoH_eq
#print axioms Eis.integral_rhoH_eq
#print axioms Eis.muR_rhoT3
#print axioms Eis.conj_psTerm_mul
#print axioms Eis.conj_pseis_mul
#print axioms Eis.integral_conj_pseis_mul
#print axioms Eis.inner_toLp_pseis
