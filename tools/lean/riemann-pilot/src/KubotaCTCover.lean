import KubotaCTPrinciple

/-! # The constant-term principle for translates (round 439)

S5f-11 of round 360's plan, part 2. Round 438's next step planned the second sentence of S5f-11, "So a
combination of its translates whose constant terms all vanish is zero", through traces to `Γ_1(3)`. This round
proves it for θ's representative `θ̃` (round 425's `thetaF`), with `r > 0`, `Y > 0`, `ν = ρ_G dμ` as in round
423 and `κ` Kubota's character:

* **Change of variables** (**`integral_muR_actP`** and **`integral_muR_slAct`**, with `actP_one`,
  `det_inv_eq_one`, `actP_inv_actP`, `actP_actP_inv`, `lintegral_muR_actP` and `lintegral_muR_slAct`):
  `∫G(g·p) dν_ρ = ∫G dν_{ρ∘g⁻¹}` for `det g = 1` (round 383's `integral_actP`).
* **Partitions of unity for conjugate groups, and independence** (**`isPU_comp_actP_inv`** and
  **`integral_isPU_eq`**): for `e : H ≃ H′` with `e(γ)·(g·p) = g·(γ·p)`, `ρ∘g⁻¹` is a partition of unity for
  `H′` when `ρ` is one for `H`; and `∫G dν_ρ` does not depend on the partition of unity `ρ`, for `G` invariant
  and integrable (round 386's `lintegral_isPU_eq`, through the positive and negative parts of the real and
  imaginary parts).
* **Folding and the trace** (`trK`, a definition; **`integral_puLe_eq`** and **`isAut_trK`**, with
  `rhoG_lt_top`, `measurable_puLe`, `rhoG_slAct_le_puLe` and `measurable_trK`): with round 386's partition of
  unity `ρ_H = Σ_q ρ_G(q·)` over the cosets `q` of `H ∩ Γ_1(3)` in `Γ_1(3)`, finitely many,
  `∫G dν_{ρ_H} = ∫Σ_q G(q⁻¹·p) dν`; the trace `Tr f = Σ_q conj κ(q⁻¹)·f∘q⁻¹` of a function automorphic on `H`
  is automorphic on `Γ_1(3)`.
* **Translates** (**`isAut_comp_actP`**, **`isAut_comp_actP_inv`** and **`integral_conj_comp_actP_mul`**, with
  `lintegral_puLe_eq_comp_actP` and `lintegral_slAct_inv_le_puLe`): if moreover `κ(e(γ)) = κ(γ)`, then `F∘g`
  is automorphic on `H` when `F` is on `H′`, `D∘g⁻¹` is automorphic on `H′` when `D` is on `H`, and
  `∫conj F(g·p)·D(p) dν_{ρ_H} = ∫conj F·Tr(D∘g⁻¹) dν` for `F` automorphic on `Γ_1(3)` and `H′ ≤ Γ_1(3)` of
  finite index.
* **The principle** (**`translates_eq_zero`**, with `ae_eq_zero_of_isPU`): for `D = Σ_j c_j·θ̃∘g_j`, with such
  data `(g_j, H′_j, e_j)` on one `H ≤ Γ_1(3)`, `∫|D|² dν_{ρ_H} = Σ_i conj(c_i)·⟨θ, Tr_i⟩`, `Tr_i` the trace of
  `D∘g_i⁻¹`. So if the constant term at `∞` of every `Tr_i` vanishes for almost every `v > 0`, round 438's
  principle gives `∫|D|² dν_{ρ_H} = 0`, and `D = 0` almost everywhere on upper half-space.
-/

open MeasureTheory Set Filter NumberField Complex
open scoped ENNReal Topology MatrixGroups ComplexConjugate

noncomputable section

namespace Eis

/-! ### Change of variables -/

theorem actP_one (p : ℂ × ℝ) : actP (1 : Matrix (Fin 2) (Fin 2) ℂ) p = p := by
  simp [actP, uhsAct, uhsZ, uhsV, uhsDen]

theorem det_inv_eq_one {g : Matrix (Fin 2) (Fin 2) ℂ} (hg : g.det = 1) : g⁻¹.det = 1 := by
  rw [Matrix.det_nonsing_inv, hg, Ring.inverse_one]

theorem actP_inv_actP {g : Matrix (Fin 2) (Fin 2) ℂ} (hg : g.det = 1) {p : ℂ × ℝ} (hp : p ∈ UHS) :
    actP g⁻¹ (actP g p) = p := by
  rw [← actP_mul (det_inv_eq_one hg) hg hp,
    Matrix.nonsing_inv_mul _ (by rw [hg]; exact isUnit_one), actP_one]

theorem actP_actP_inv {g : Matrix (Fin 2) (Fin 2) ℂ} (hg : g.det = 1) {p : ℂ × ℝ} (hp : p ∈ UHS) :
    actP g (actP g⁻¹ p) = p := by
  rw [← actP_mul hg (det_inv_eq_one hg) hp,
    Matrix.mul_nonsing_inv _ (by rw [hg]; exact isUnit_one), actP_one]

/-- **Change of variables in `[0, ∞]`**: `∫G(g·p) dν_ρ = ∫G dν_{ρ∘g⁻¹}` for `det g = 1`. -/
theorem lintegral_muR_actP {g : Matrix (Fin 2) (Fin 2) ℂ} (hg : g.det = 1) {ρ : ℂ × ℝ → ℝ≥0∞}
    (hρ : Measurable ρ) {G : ℂ × ℝ → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ p, G (actP g p) ∂(muR ρ) = ∫⁻ p, G p ∂(muR fun p => ρ (actP g⁻¹ p)) := by
  have hρ' : Measurable fun p => ρ (actP g⁻¹ p) := hρ.comp (measurable_actP _)
  rw [muR, muR, lintegral_withDensity_eq_lintegral_mul _ hρ
      (show Measurable fun p => G (actP g p) from hG.comp (measurable_actP g)),
    lintegral_withDensity_eq_lintegral_mul _ hρ' hG]
  simp only [Pi.mul_apply]
  rw [← lintegral_actP hg (F := fun p => ρ (actP g⁻¹ p) * G p) (hρ'.mul hG)]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_UHS] with p hp
  simp only [actP_inv_actP hg hp]

/-- **Change of variables**: `∫G(g·p) dν_ρ = ∫G dν_{ρ∘g⁻¹}` for `det g = 1` and `ρ` finite on upper
half-space. -/
theorem integral_muR_actP {g : Matrix (Fin 2) (Fin 2) ℂ} (hg : g.det = 1) {ρ : ℂ × ℝ → ℝ≥0∞}
    (hρ : Measurable ρ) (hρt : ∀ p ∈ UHS, ρ p < ⊤) {G : ℂ × ℝ → ℂ} (hG : Measurable G) :
    ∫ p, G (actP g p) ∂(muR ρ) = ∫ p, G p ∂(muR fun p => ρ (actP g⁻¹ p)) := by
  have hρ' : Measurable fun p => ρ (actP g⁻¹ p) := hρ.comp (measurable_actP _)
  have h1 : ∀ᵐ p ∂uhsMeasure, ρ p < ⊤ := by
    filter_upwards [ae_UHS] with p hp
    exact hρt p hp
  have h2 : ∀ᵐ p ∂uhsMeasure, ρ (actP g⁻¹ p) < ⊤ := by
    filter_upwards [ae_UHS] with p hp
    exact hρt _ (actP_mem (det_inv_eq_one hg) hp)
  rw [muR, muR, integral_withDensity_eq_integral_toReal_smul hρ h1,
    integral_withDensity_eq_integral_toReal_smul hρ' h2,
    ← integral_actP hg (F := fun p => (ρ (actP g⁻¹ p)).toReal • G p)
      ((hρ'.ennreal_toReal.smul hG).aestronglyMeasurable)]
  refine integral_congr_ae ?_
  filter_upwards [ae_UHS] with p hp
  simp only [actP_inv_actP hg hp]

/-- **Change of variables by an element of `SL_2(ℤ[ω])`**: `∫G dν_{ρ∘γ} = ∫G(γ⁻¹·p) dν_ρ`. -/
theorem integral_muR_slAct (γ : SL(2, 𝓞 K)) {ρ : ℂ × ℝ → ℝ≥0∞} (hρ : Measurable ρ)
    (hρt : ∀ p ∈ UHS, ρ p < ⊤) {G : ℂ × ℝ → ℂ} (hG : Measurable G) :
    ∫ p, G p ∂(muR fun p => ρ (slAct γ p)) = ∫ p, G (slAct γ⁻¹ p) ∂(muR ρ) := by
  have hρ' : Measurable fun p => ρ (slAct γ p) := hρ.comp (measurable_slAct _)
  have h1 : ∀ᵐ p ∂uhsMeasure, ρ p < ⊤ := by
    filter_upwards [ae_UHS] with p hp
    exact hρt p hp
  have h2 : ∀ᵐ p ∂uhsMeasure, ρ (slAct γ p) < ⊤ := by
    filter_upwards [ae_UHS] with p hp
    exact hρt _ (slAct_mem _ hp)
  rw [muR, muR, integral_withDensity_eq_integral_toReal_smul hρ' h2,
    integral_withDensity_eq_integral_toReal_smul hρ h1,
    ← integral_actP (det_map_σO γ⁻¹.2) (F := fun p => (ρ (slAct γ p)).toReal • G p)
      ((hρ'.ennreal_toReal.smul hG).aestronglyMeasurable)]
  refine integral_congr_ae ?_
  filter_upwards [ae_UHS] with p hp
  show (ρ (slAct γ (slAct γ⁻¹ p))).toReal • G (slAct γ⁻¹ p) = _
  rw [slAct_slAct_inv _ hp]

/-- **Change of variables by an element of `SL_2(ℤ[ω])`, in `[0, ∞]`**: `∫G dν_{ρ∘γ} = ∫G(γ⁻¹·p) dν_ρ`. -/
theorem lintegral_muR_slAct (γ : SL(2, 𝓞 K)) {ρ : ℂ × ℝ → ℝ≥0∞} (hρ : Measurable ρ)
    {G : ℂ × ℝ → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ p, G p ∂(muR fun p => ρ (slAct γ p)) = ∫⁻ p, G (slAct γ⁻¹ p) ∂(muR ρ) := by
  have hρ' : Measurable fun p => ρ (slAct γ p) := hρ.comp (measurable_slAct _)
  rw [muR, muR, lintegral_withDensity_eq_lintegral_mul _ hρ' hG,
    lintegral_withDensity_eq_lintegral_mul _ hρ
      (show Measurable fun p => G (slAct γ⁻¹ p) from hG.comp (measurable_slAct _))]
  simp only [Pi.mul_apply]
  rw [← lintegral_slAct γ⁻¹ (F := fun p => ρ (slAct γ p) * G p) (hρ'.mul hG)]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_UHS] with p hp
  rw [slAct_slAct_inv _ hp]

/-! ### Partitions of unity for conjugate groups, and independence -/

/-- **A partition of unity for a conjugate group**: for `e : H ≃ H′` with `e(γ)·(g·p) = g·(γ·p)` and `ρ` a
partition of unity for `H`, `ρ∘g⁻¹` is one for `H′`. -/
theorem isPU_comp_actP_inv {H H' : Subgroup SL(2, 𝓞 K)} {g : Matrix (Fin 2) (Fin 2) ℂ}
    (hg : g.det = 1) (e : H ≃ H') (he : ∀ γ : H, ∀ p ∈ UHS, slAct (e γ) (actP g p) = actP g (slAct γ p))
    {ρ : ℂ × ℝ → ℝ≥0∞} (hρ : IsPU H ρ) : IsPU H' fun p => ρ (actP g⁻¹ p) := by
  refine ⟨hρ.1.comp (measurable_actP _), fun p hp => ?_⟩
  have hq : actP g⁻¹ p ∈ UHS := actP_mem (det_inv_eq_one hg) hp
  rw [← hρ.2 _ hq]
  refine (e.tsum_eq (fun γ' : H' => ρ (actP g⁻¹ (slAct γ' p)))).symm.trans (tsum_congr fun γ => ?_)
  have h := he γ (actP g⁻¹ p) hq
  rw [actP_actP_inv hg hp] at h
  rw [h, actP_inv_actP hg (slAct_mem _ hq)]

/-- **The integral over `Γ\H³` of a complex function does not depend on the partition of unity**, for `G`
measurable and invariant under `Γ` with `∫|G| dν_ρ < ∞`. -/
theorem integral_isPU_eq {Γ : Subgroup SL(2, 𝓞 K)} {ρ ρ' : ℂ × ℝ → ℝ≥0∞} (hρ : IsPU Γ ρ)
    (hρ' : IsPU Γ ρ') {G : ℂ × ℝ → ℂ} (hG : Measurable G)
    (hinv : ∀ γ ∈ Γ, ∀ p ∈ UHS, G (slAct γ p) = G p) (hint : ∫⁻ p, ‖G p‖ₑ ∂(muR ρ) < ⊤) :
    ∫ p, G p ∂(muR ρ) = ∫ p, G p ∂(muR ρ') := by
  have hl : ∀ F : ℂ × ℝ → ℝ≥0∞, Measurable F → (∀ γ ∈ Γ, ∀ p ∈ UHS, F (slAct γ p) = F p) →
      ∫⁻ p, F p ∂(muR ρ) = ∫⁻ p, F p ∂(muR ρ') := fun F hF hFi => by
    rw [muR, muR, lintegral_withDensity_eq_lintegral_mul _ hρ.1 hF,
      lintegral_withDensity_eq_lintegral_mul _ hρ'.1 hF]
    exact lintegral_isPU_eq hρ hρ' hF hFi
  have hint' : ∫⁻ p, ‖G p‖ₑ ∂(muR ρ') < ⊤ := by
    rw [← hl _ hG.enorm fun γ hγ p hp => by rw [hinv γ hγ p hp]]
    exact hint
  have hi : Integrable G (muR ρ) := ⟨hG.aestronglyMeasurable, hint⟩
  have hi' : Integrable G (muR ρ') := ⟨hG.aestronglyMeasurable, hint'⟩
  have hreal : ∀ u : ℂ × ℝ → ℝ, Measurable u → (∀ γ ∈ Γ, ∀ p ∈ UHS, u (slAct γ p) = u p) →
      Integrable u (muR ρ) → Integrable u (muR ρ') →
      ∫ p, u p ∂(muR ρ) = ∫ p, u p ∂(muR ρ') := by
    intro u hu hui h1 h2
    rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part h1,
      integral_eq_lintegral_pos_part_sub_lintegral_neg_part h2,
      hl (fun p => ENNReal.ofReal (u p)) (ENNReal.measurable_ofReal.comp hu) fun γ hγ p hp => by
        simp only [hui γ hγ p hp],
      hl (fun p => ENNReal.ofReal (-u p)) (ENNReal.measurable_ofReal.comp hu.neg) fun γ hγ p hp => by
        simp only [hui γ hγ p hp]]
  apply Complex.ext
  · have e1 := integral_re hi
    have e2 := integral_re hi'
    simp only [RCLike.re_to_complex] at e1 e2
    rw [← e1, ← e2]
    exact hreal _ (Complex.measurable_re.comp hG) (fun γ hγ p hp => by simp only [hinv γ hγ p hp])
      hi.re hi'.re
  · have e1 := integral_im hi
    have e2 := integral_im hi'
    simp only [RCLike.im_to_complex] at e1 e2
    rw [← e1, ← e2]
    exact hreal _ (Complex.measurable_im.comp hG) (fun γ hγ p hp => by simp only [hinv γ hγ p hp])
      hi.im hi'.im

/-! ### Folding over the cosets of a subgroup of finite index -/

theorem rhoG_lt_top {p : ℂ × ℝ} (hp : p ∈ UHS) : rhoG p < ⊤ :=
  lt_of_le_of_lt (isPU_rhoG.le_one hp) ENNReal.one_lt_top

theorem measurable_puLe (H : Subgroup SL(2, 𝓞 K)) : Measurable (puLe Gam3 H rhoG) :=
  Measurable.tsum fun _ => isPU_rhoG.1.comp (measurable_slAct _)

/-- `ρ_G(q·p) ≤ ρ_H(p)` for `ρ_H = Σ_{q∈Γ_1(3)/H} ρ_G(q·)`. -/
theorem rhoG_slAct_le_puLe {H : Subgroup SL(2, 𝓞 K)} (q : Gam3 ⧸ H.subgroupOf Gam3) (p : ℂ × ℝ) :
    rhoG (slAct (q.out : SL(2, 𝓞 K)) p) ≤ puLe Gam3 H rhoG p :=
  ENNReal.le_tsum (f := fun q : Gam3 ⧸ H.subgroupOf Gam3 => rhoG (slAct (q.out : SL(2, 𝓞 K)) p)) q

/-- **Folding**: for `H ≤ Γ_1(3)` of finite index and `ρ_H = Σ_{q∈Γ_1(3)/H} ρ_G(q·)`,
`∫G dν_{ρ_H} = ∫Σ_q G(q⁻¹·p) dν`. -/
theorem integral_puLe_eq {H : Subgroup SL(2, 𝓞 K)} [Finite (Gam3 ⧸ H.subgroupOf Gam3)]
    {G : ℂ × ℝ → ℂ} (hG : Measurable G) (hint : ∫⁻ p, ‖G p‖ₑ ∂(muR (puLe Gam3 H rhoG)) < ⊤) :
    ∫ p, G p ∂(muR (puLe Gam3 H rhoG)) =
      ∫ p, ∑' q : Gam3 ⧸ H.subgroupOf Gam3, G (slAct (q.out : SL(2, 𝓞 K))⁻¹ p) ∂(muR rhoG) := by
  classical
  have := Fintype.ofFinite (Gam3 ⧸ H.subgroupOf Gam3)
  set ρq : Gam3 ⧸ H.subgroupOf Gam3 → ℂ × ℝ → ℝ≥0∞ := fun q p => rhoG (slAct (q.out : SL(2, 𝓞 K)) p)
    with hρqdef
  have hρq : ∀ q, Measurable (ρq q) := fun q => isPU_rhoG.1.comp (measurable_slAct _)
  have hsum : muR (puLe Gam3 H rhoG) = Measure.sum fun q => muR (ρq q) := by
    have e : puLe Gam3 H rhoG = ∑' q, ρq q := by
      funext p
      rw [ENNReal.tsum_apply]
      rfl
    rw [muR, e, withDensity_tsum hρq]
    rfl
  have hint' : Integrable G (Measure.sum fun q => muR (ρq q)) := by
    rw [← hsum]
    exact ⟨hG.aestronglyMeasurable, hint⟩
  have hi : ∀ q : Gam3 ⧸ H.subgroupOf Gam3,
      Integrable (fun p => G (slAct (q.out : SL(2, 𝓞 K))⁻¹ p)) (muR rhoG) := by
    intro q
    refine ⟨(hG.comp (measurable_slAct _)).aestronglyMeasurable, ?_⟩
    show ∫⁻ p, ‖G (slAct (q.out : SL(2, 𝓞 K))⁻¹ p)‖ₑ ∂(muR rhoG) < ⊤
    rw [← lintegral_muR_slAct (q.out : SL(2, 𝓞 K)) isPU_rhoG.1 hG.enorm]
    refine lt_of_le_of_lt ?_ hint
    rw [muR, muR, lintegral_withDensity_eq_lintegral_mul _ (hρq q) hG.enorm,
      lintegral_withDensity_eq_lintegral_mul _ (measurable_puLe H) hG.enorm]
    exact lintegral_mono fun p => by
      simp only [Pi.mul_apply]
      gcongr
      exact rhoG_slAct_le_puLe q p
  rw [hsum, integral_sum_measure hint']
  have hterm : ∀ q, ∫ p, G p ∂muR (ρq q) = ∫ p, G (slAct (q.out : SL(2, 𝓞 K))⁻¹ p) ∂(muR rhoG) :=
    fun q => integral_muR_slAct (q.out : SL(2, 𝓞 K)) isPU_rhoG.1 (fun p hp => rhoG_lt_top hp) hG
  simp_rw [hterm]
  rw [tsum_fintype]
  simp_rw [tsum_fintype]
  rw [integral_finsetSum _ fun q _ => hi q]

/-! ### The trace to `Γ_1(3)` -/

/-- **The trace to `Γ_1(3)`** with Kubota's character, for `H ≤ Γ_1(3)`:
`Σ_{q∈Γ_1(3)/H} conj κ(q⁻¹)·f(q⁻¹·p)`. -/
def trK (H : Subgroup SL(2, 𝓞 K)) (f : ℂ × ℝ → ℂ) (p : ℂ × ℝ) : ℂ :=
  ∑' q : Gam3 ⧸ H.subgroupOf Gam3,
    conj (kub ↑((q.out : SL(2, 𝓞 K))⁻¹)) * f (slAct (q.out : SL(2, 𝓞 K))⁻¹ p)

theorem measurable_trK {H : Subgroup SL(2, 𝓞 K)} [Finite (Gam3 ⧸ H.subgroupOf Gam3)]
    {f : ℂ × ℝ → ℂ} (hf : Measurable f) : Measurable (trK H f) := by
  classical
  have := Fintype.ofFinite (Gam3 ⧸ H.subgroupOf Gam3)
  unfold trK
  simp_rw [tsum_fintype]
  exact Finset.measurable_sum _ fun q _ => measurable_const.mul (hf.comp (measurable_slAct _))

/-- **The trace is automorphic on `Γ_1(3)`** with Kubota's character, for `f` automorphic on `H`. -/
theorem isAut_trK {H : Subgroup SL(2, 𝓞 K)} {f : ℂ × ℝ → ℂ}
    (hf : IsAut H (fun g => kub ↑g) f) : IsAut Gam3 (fun g => kub ↑g) (trK H f) := by
  intro δ hδ p hp
  set δ' : Gam3 := ⟨δ, hδ⟩ with hδ'
  unfold trK
  rw [← (MulAction.toPerm δ' : Equiv.Perm (Gam3 ⧸ H.subgroupOf Gam3)).tsum_eq, ← tsum_mul_left]
  refine tsum_congr fun q => ?_
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (H.subgroupOf Gam3) (δ' * q.out)
  have e1 : (MulAction.toPerm δ' q : Gam3 ⧸ H.subgroupOf Gam3) =
      (QuotientGroup.mk (δ' * q.out) : Gam3 ⧸ H.subgroupOf Gam3) := by
    rw [MulAction.toPerm_apply]
    calc δ' • q = δ' • (QuotientGroup.mk q.out : Gam3 ⧸ H.subgroupOf Gam3) := by
          rw [QuotientGroup.out_eq']
      _ = QuotientGroup.mk (δ' * q.out) := rfl
  rw [e1, hh]
  have hhH : ((h : Gam3) : SL(2, 𝓞 K)) ∈ H := Subgroup.mem_subgroupOf.mp h.2
  have hhG : ((h : Gam3) : SL(2, 𝓞 K)) ∈ Gam3 := (h : Gam3).2
  have hqG : ((q.out : Gam3) : SL(2, 𝓞 K)) ∈ Gam3 := q.out.2
  have e2 : (((δ' * q.out * h : Gam3)) : SL(2, 𝓞 K))⁻¹ =
      ((h : Gam3) : SL(2, 𝓞 K))⁻¹ * (((q.out : Gam3) : SL(2, 𝓞 K))⁻¹ * δ⁻¹) := by
    simp only [Subgroup.coe_mul, hδ', mul_inv_rev, mul_assoc]
  have hq' : slAct ((q.out : Gam3) : SL(2, 𝓞 K))⁻¹ p ∈ UHS := slAct_mem _ hp
  rw [e2, slAct_mul _ _ (slAct_mem _ hp), slAct_mul _ _ (slAct_mem _ hp), slAct_inv_slAct _ hp,
    hf _ (H.inv_mem hhH) _ hq']
  have hk1 : kub ↑(((h : Gam3) : SL(2, 𝓞 K))⁻¹ * (((q.out : Gam3) : SL(2, 𝓞 K))⁻¹ * δ⁻¹)) =
      kub ↑(((h : Gam3) : SL(2, 𝓞 K))⁻¹) * (kub ↑(((q.out : Gam3) : SL(2, 𝓞 K))⁻¹) * kub ↑δ⁻¹) := by
    rw [kub_mul_Gam3 (Gam3.inv_mem hhG) (Gam3.mul_mem (Gam3.inv_mem hqG) (Gam3.inv_mem hδ)),
      kub_mul_Gam3 (Gam3.inv_mem hqG) (Gam3.inv_mem hδ)]
  rw [hk1, kub_inv_Gam3 hδ]
  have hk2 := kub_mul_conj_kub (Gam3.inv_mem hhG)
  simp only [map_mul, Complex.conj_conj]
  linear_combination (conj (kub ↑(((q.out : Gam3) : SL(2, 𝓞 K))⁻¹)) * kub ↑δ *
    f (slAct ((q.out : Gam3) : SL(2, 𝓞 K))⁻¹ p)) * hk2

/-! ### Translates -/

/-- **A translate of an automorphic function is automorphic on the cover**: for `e : H ≃ H′` with
`e(γ)·(g·p) = g·(γ·p)` and `κ(e(γ)) = κ(γ)`, `F∘g` is automorphic on `H` when `F` is automorphic on `H′`. -/
theorem isAut_comp_actP {H H' : Subgroup SL(2, 𝓞 K)} {g : Matrix (Fin 2) (Fin 2) ℂ} (hg : g.det = 1)
    (e : H ≃ H') (he : ∀ γ : H, ∀ p ∈ UHS, slAct (e γ) (actP g p) = actP g (slAct γ p))
    (hκ : ∀ γ : H, kub ↑(e γ : SL(2, 𝓞 K)) = kub ↑(γ : SL(2, 𝓞 K))) {F : ℂ × ℝ → ℂ}
    (hF : IsAut H' (fun g => kub ↑g) F) : IsAut H (fun g => kub ↑g) fun p => F (actP g p) := by
  intro γ hγ p hp
  have h := he ⟨γ, hγ⟩ p hp
  show F (actP g (slAct γ p)) = kub ↑γ * F (actP g p)
  rw [← h, hF _ (e ⟨γ, hγ⟩).2 _ (actP_mem hg hp)]
  exact congrArg (· * F (actP g p)) (hκ ⟨γ, hγ⟩)

/-- **The inverse translate**: `D∘g⁻¹` is automorphic on `H′` when `D` is automorphic on `H`. -/
theorem isAut_comp_actP_inv {H H' : Subgroup SL(2, 𝓞 K)} {g : Matrix (Fin 2) (Fin 2) ℂ}
    (hg : g.det = 1) (e : H ≃ H')
    (he : ∀ γ : H, ∀ p ∈ UHS, slAct (e γ) (actP g p) = actP g (slAct γ p))
    (hκ : ∀ γ : H, kub ↑(e γ : SL(2, 𝓞 K)) = kub ↑(γ : SL(2, 𝓞 K))) {D : ℂ × ℝ → ℂ}
    (hD : IsAut H (fun g => kub ↑g) D) : IsAut H' (fun g => kub ↑g) fun p => D (actP g⁻¹ p) := by
  intro γ' hγ' p hp
  set γ := e.symm ⟨γ', hγ'⟩ with hγdef
  have hq : actP g⁻¹ p ∈ UHS := actP_mem (det_inv_eq_one hg) hp
  have h := he γ (actP g⁻¹ p) hq
  rw [actP_actP_inv hg hp, hγdef, Equiv.apply_symm_apply] at h
  show D (actP g⁻¹ (slAct γ' p)) = kub ↑γ' * D (actP g⁻¹ p)
  rw [show slAct γ' p = actP g (slAct (γ : SL(2, 𝓞 K)) (actP g⁻¹ p)) from h,
    actP_inv_actP hg (slAct_mem _ hq), hD _ γ.2 _ hq]
  have hk : kub ↑(γ' : SL(2, 𝓞 K)) = kub ↑((γ : H) : SL(2, 𝓞 K)) := by
    have := hκ γ
    rwa [hγdef, Equiv.apply_symm_apply] at this
  exact congrArg (· * D (actP g⁻¹ p)) hk.symm

/-! ### The pairing of a translate with a function on the cover -/

/-- **Unfolding a translate**: for `F` automorphic on `Γ_1(3)`, `D` automorphic on `H`, `e : H ≃ H′`
intertwining `g` with `κ` preserved, `H′ ≤ Γ_1(3)` of finite index, and `ρ_H` a partition of unity for `H`,
`∫conj F(g·p)·D(p) dν_{ρ_H} = ∫conj F·Tr(D∘g⁻¹) dν`. -/
theorem integral_conj_comp_actP_mul {H H' : Subgroup SL(2, 𝓞 K)} (hH' : H' ≤ Gam3)
    [Finite (Gam3 ⧸ H'.subgroupOf Gam3)] {g : Matrix (Fin 2) (Fin 2) ℂ} (hg : g.det = 1) (e : H ≃ H')
    (he : ∀ γ : H, ∀ p ∈ UHS, slAct (e γ) (actP g p) = actP g (slAct γ p))
    (hκ : ∀ γ : H, kub ↑(e γ : SL(2, 𝓞 K)) = kub ↑(γ : SL(2, 𝓞 K))) {ρH : ℂ × ℝ → ℝ≥0∞}
    (hρH : IsPU H ρH) {F : ℂ × ℝ → ℂ} (hFm : Measurable F) (hF : IsAut Gam3 (fun g => kub ↑g) F)
    {D : ℂ × ℝ → ℂ} (hDm : Measurable D) (hD : IsAut H (fun g => kub ↑g) D)
    (hint : ∫⁻ p, ‖conj (F (actP g p)) * D p‖ₑ ∂(muR ρH) < ⊤) :
    ∫ p, conj (F (actP g p)) * D p ∂(muR ρH) =
      ∫ p, conj (F p) * trK H' (fun p => D (actP g⁻¹ p)) p ∂(muR rhoG) := by
  set G : ℂ × ℝ → ℂ := fun p => conj (F p) * D (actP g⁻¹ p) with hGdef
  have hGm : Measurable G :=
    (Complex.continuous_conj.measurable.comp hFm).mul (hDm.comp (measurable_actP _))
  have hρt : ∀ p ∈ UHS, ρH p < ⊤ := fun p hp => lt_of_le_of_lt (hρH.le_one hp) ENNReal.one_lt_top
  have e1 : ∫ p, conj (F (actP g p)) * D p ∂(muR ρH) = ∫ p, G (actP g p) ∂(muR ρH) := by
    refine integral_congr_ae ?_
    filter_upwards [ae_muR_UHS ρH] with p hp
    simp only [hGdef, actP_inv_actP hg hp]
  have hDinv := isAut_comp_actP_inv hg e he hκ hD
  have hGinv : ∀ γ ∈ H', ∀ p ∈ UHS, G (slAct γ p) = G p := by
    intro γ hγ p hp
    have h2 := hDinv γ hγ p hp
    simp only at h2
    simp only [hGdef]
    rw [hF γ (hH' hγ) p hp, h2]
    have h1 := kub_mul_conj_kub (hH' hγ)
    simp only [map_mul]
    linear_combination (conj (F p) * D (actP g⁻¹ p)) * h1
  have hint2 : ∫⁻ p, ‖G p‖ₑ ∂(muR fun p => ρH (actP g⁻¹ p)) < ⊤ := by
    rw [← lintegral_muR_actP hg hρH.1 hGm.enorm]
    refine lt_of_le_of_lt (le_of_eq (lintegral_congr_ae ?_)) hint
    filter_upwards [ae_muR_UHS ρH] with p hp
    simp only [hGdef, actP_inv_actP hg hp]
  have hPU1 : IsPU H' fun p => ρH (actP g⁻¹ p) := isPU_comp_actP_inv hg e he hρH
  have hPU2 : IsPU H' (puLe Gam3 H' rhoG) := isPU_puLe hH' isPU_rhoG
  have hint3 : ∫⁻ p, ‖G p‖ₑ ∂(muR (puLe Gam3 H' rhoG)) < ⊤ := by
    have h := lintegral_isPU_eq hPU1 hPU2 (F := fun p => ‖G p‖ₑ) hGm.enorm
      (fun γ hγ p hp => by simp only [hGinv γ hγ p hp])
    rw [muR, lintegral_withDensity_eq_lintegral_mul _ hPU2.1 hGm.enorm]
    rw [muR, lintegral_withDensity_eq_lintegral_mul _ hPU1.1 hGm.enorm] at hint2
    simp only [Pi.mul_apply] at hint2 ⊢
    rw [← h]
    exact hint2
  rw [e1, integral_muR_actP hg hρH.1 hρt hGm, integral_isPU_eq hPU1 hPU2 hGm hGinv hint2,
    integral_puLe_eq hGm hint3]
  refine integral_congr_ae ?_
  filter_upwards [ae_muR_UHS rhoG] with p hp
  unfold trK
  rw [← tsum_mul_left]
  refine tsum_congr fun q => ?_
  simp only [hGdef]
  rw [hF _ (Gam3.inv_mem q.out.2) p hp]
  simp only [map_mul]
  ring

/-! ### Integrals over the cover -/

/-- **An integral over `H′\H³` as an integral over `H\H³`**: for `e : H ≃ H′` intertwining `g`, `H′ ≤ Γ_1(3)`,
`ρ_H` a partition of unity for `H` and `F` measurable and invariant under `H′`,
`∫F dν_{ρ_{H′}} = ∫F(g·p) dν_{ρ_H}`. -/
theorem lintegral_puLe_eq_comp_actP {H H' : Subgroup SL(2, 𝓞 K)} (hH' : H' ≤ Gam3)
    {g : Matrix (Fin 2) (Fin 2) ℂ} (hg : g.det = 1) (e : H ≃ H')
    (he : ∀ γ : H, ∀ p ∈ UHS, slAct (e γ) (actP g p) = actP g (slAct γ p)) {ρH : ℂ × ℝ → ℝ≥0∞}
    (hρH : IsPU H ρH) {F : ℂ × ℝ → ℝ≥0∞} (hF : Measurable F)
    (hinv : ∀ γ ∈ H', ∀ p ∈ UHS, F (slAct γ p) = F p) :
    ∫⁻ p, F p ∂(muR (puLe Gam3 H' rhoG)) = ∫⁻ p, F (actP g p) ∂(muR ρH) := by
  have hPU1 : IsPU H' fun p => ρH (actP g⁻¹ p) := isPU_comp_actP_inv hg e he hρH
  have hPU2 : IsPU H' (puLe Gam3 H' rhoG) := isPU_puLe hH' isPU_rhoG
  rw [lintegral_muR_actP hg hρH.1 hF, muR, muR, lintegral_withDensity_eq_lintegral_mul _ hPU2.1 hF,
    lintegral_withDensity_eq_lintegral_mul _ hPU1.1 hF]
  exact (lintegral_isPU_eq hPU1 hPU2 hF hinv).symm

/-- `∫F(q⁻¹·p) dν ≤ ∫F dν_{ρ_H}` for a coset `q` of `H` in `Γ_1(3)`. -/
theorem lintegral_slAct_inv_le_puLe {H : Subgroup SL(2, 𝓞 K)} (q : Gam3 ⧸ H.subgroupOf Gam3)
    {F : ℂ × ℝ → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ p, F (slAct (q.out : SL(2, 𝓞 K))⁻¹ p) ∂(muR rhoG) ≤ ∫⁻ p, F p ∂(muR (puLe Gam3 H rhoG)) := by
  rw [← lintegral_muR_slAct (q.out : SL(2, 𝓞 K)) isPU_rhoG.1 hF, muR, muR,
    lintegral_withDensity_eq_lintegral_mul _
      (show Measurable fun p => rhoG (slAct (q.out : SL(2, 𝓞 K)) p) from
        isPU_rhoG.1.comp (measurable_slAct _)) hF,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_puLe H) hF]
  exact lintegral_mono fun p => by
    simp only [Pi.mul_apply]
    gcongr
    exact rhoG_slAct_le_puLe q p

/-! ### The principle -/

/-- **A null set on a fundamental domain is null**: for `ρ` a partition of unity for `H` and `D` measurable
with `|D|` invariant under `H`, `D = 0` almost everywhere on upper half-space if `D = 0` for `ν_ρ`-almost
every point. -/
theorem ae_eq_zero_of_isPU {H : Subgroup SL(2, 𝓞 K)} {ρ : ℂ × ℝ → ℝ≥0∞} (hρ : IsPU H ρ)
    {D : ℂ × ℝ → ℂ} (hDm : Measurable D) (hinv : ∀ γ ∈ H, ∀ p ∈ UHS, ‖D (slAct γ p)‖ = ‖D p‖)
    (h0 : ∀ᵐ p ∂(muR ρ), D p = 0) : ∀ᵐ p ∂uhsMeasure, D p = 0 := by
  set S : Set (ℂ × ℝ) := {p | D p ≠ 0} with hSdef
  have hS : MeasurableSet S := (measurableSet_singleton (0 : ℂ)).compl.preimage hDm
  have hSi : ∀ γ ∈ H, ∀ p ∈ UHS,
      S.indicator (1 : ℂ × ℝ → ℝ≥0∞) (slAct γ p) = S.indicator 1 p := by
    intro γ hγ p hp
    have e : slAct γ p ∈ S ↔ p ∈ S := by
      show D (slAct γ p) ≠ 0 ↔ D p ≠ 0
      rw [← norm_ne_zero_iff, hinv γ hγ p hp, norm_ne_zero_iff]
    by_cases h : p ∈ S
    · rw [indicator_of_mem h, indicator_of_mem (e.2 h)]
      rfl
    · rw [indicator_of_notMem h, indicator_of_notMem (fun h' => h (e.1 h'))]
  have h1 : ∫⁻ p, ρ p * S.indicator 1 p ∂uhsMeasure = 0 := by
    have e : ∫⁻ p, ρ p * S.indicator 1 p ∂uhsMeasure = ∫⁻ p, S.indicator 1 p ∂(muR ρ) := by
      rw [muR, lintegral_withDensity_eq_lintegral_mul _ hρ.1 (measurable_one.indicator hS)]
      rfl
    rw [e, lintegral_indicator_one hS]
    exact ae_iff.1 h0
  have h2 := lintegral_unfold hρ (Φ := fun γ p => S.indicator (1 : ℂ × ℝ → ℝ≥0∞) (slAct γ p))
    (Ψ := S.indicator 1) (fun γ => (measurable_one.indicator hS).comp (measurable_slAct _))
    (measurable_one.indicator hS) fun γ q hq => by
      rw [Subgroup.coe_inv, slAct_slAct_inv _ hq]
  have h3 : ∫⁻ p, ρ p * ∑' γ : H, S.indicator (1 : ℂ × ℝ → ℝ≥0∞) (slAct γ p) ∂uhsMeasure = 0 := by
    have e : ∀ᵐ p ∂uhsMeasure, ρ p * ∑' γ : H, S.indicator (1 : ℂ × ℝ → ℝ≥0∞) (slAct γ p) =
        (∑' _γ : H, (1 : ℝ≥0∞)) * (ρ p * S.indicator 1 p) := by
      filter_upwards [ae_UHS] with p hp
      rw [tsum_congr fun γ : H => hSi (γ : SL(2, 𝓞 K)) γ.2 p hp]
      rw [show (∑' _γ : H, S.indicator (1 : ℂ × ℝ → ℝ≥0∞) p) =
          S.indicator 1 p * ∑' _γ : H, (1 : ℝ≥0∞) by rw [← ENNReal.tsum_mul_left, mul_one]]
      ring
    rw [lintegral_congr_ae e, lintegral_const_mul _
      (show Measurable fun p => ρ p * S.indicator 1 p from hρ.1.mul (measurable_one.indicator hS)), h1,
      mul_zero]
  rw [h3] at h2
  rw [ae_iff]
  have e : {p | ¬ D p = 0} = S := rfl
  rw [e, ← lintegral_indicator_one hS, ← h2]

/-- **The constant-term principle for translates of θ**: for `r > 0`, `Y > 0`, `H ≤ Γ_1(3)`, matrices `g_i` of
determinant `1` with `e_i : H ≃ H′_i`, `e_i(γ)·(g_i·p) = g_i·(γ·p)`, `κ(e_i(γ)) = κ(γ)` and `H′_i ≤ Γ_1(3)` of
finite index, and `D = Σ_j c_j·θ̃∘g_j`: if for every `i` the trace of `D∘g_i⁻¹` to `Γ_1(3)` has constant term
`0` at `∞` for almost every `v > 0`, then `D = 0` almost everywhere on upper half-space. -/
theorem translates_eq_zero {r : ℝ} (hr : 0 < r) {Y : ℝ} (hY : 0 < Y) {H : Subgroup SL(2, 𝓞 K)}
    (hH : H ≤ Gam3) {ι : Type*} [Fintype ι] (g : ι → Matrix (Fin 2) (Fin 2) ℂ)
    (hg : ∀ i, (g i).det = 1) (H' : ι → Subgroup SL(2, 𝓞 K)) (hH' : ∀ i, H' i ≤ Gam3)
    [∀ i, Finite (Gam3 ⧸ (H' i).subgroupOf Gam3)] (e : ∀ i, H ≃ H' i)
    (he : ∀ i, ∀ γ : H, ∀ p ∈ UHS, slAct (e i γ) (actP (g i) p) = actP (g i) (slAct γ p))
    (hκ : ∀ i, ∀ γ : H, kub ↑(e i γ : SL(2, 𝓞 K)) = kub ↑(γ : SL(2, 𝓞 K))) (c : ι → ℂ)
    (h0 : ∀ i, ∀ᵐ v ∂(volume.restrict (Ioi (0 : ℝ))), ∫ z in fundP3,
      trK (H' i) (fun p => ∑ j, c j * thetaF r Y hY (actP (g j) (actP (g i)⁻¹ p))) (z, v) = 0) :
    ∀ᵐ p ∂uhsMeasure, ∑ j, c j * thetaF r Y hY (actP (g j) p) = 0 := by
  classical
  set θt := thetaF r Y hY with hθt
  set D : ℂ × ℝ → ℂ := fun p => ∑ j, c j * θt (actP (g j) p) with hDdef
  set ρH := puLe Gam3 H rhoG with hρHdef
  have hρH : IsPU H ρH := isPU_puLe hH isPU_rhoG
  have hθm : Measurable θt := measurable_thetaF r Y hY
  have hθaut : IsAut Gam3 (fun g => kub ↑g) θt := isAut_thetaF r Y hY
  have hθ2 : MemLp θt 2 (muR rhoG) := memLp_thetaF hr hY
  have hθinv : ∀ γ ∈ Gam3, ∀ p ∈ UHS, ‖θt (slAct γ p)‖ₑ = ‖θt p‖ₑ := enorm_slAct_of_isAut hθaut
  -- the translates
  have hTm : ∀ j, Measurable fun p => θt (actP (g j) p) := fun j => hθm.comp (measurable_actP _)
  have hTaut : ∀ j, IsAut H (fun g => kub ↑g) fun p => θt (actP (g j) p) := fun j =>
    isAut_comp_actP (hg j) (e j) (he j) (hκ j) fun γ hγ p hp => hθaut γ (hH' j hγ) p hp
  have hT2 : ∀ j, MemLp (fun p => θt (actP (g j) p)) 2 (muR ρH) := by
    intro j
    refine memLp_two_of_lintegral (hTm j) ?_
    have hm2 : Measurable fun p => ‖θt p‖ₑ ^ 2 := hθm.enorm.pow_const 2
    rw [← lintegral_puLe_eq_comp_actP (hH' j) (hg j) (e j) (he j) hρH (F := fun p => ‖θt p‖ₑ ^ 2) hm2
      fun γ hγ p hp => by rw [hθinv γ (hH' j hγ) p hp], muR,
      lintegral_withDensity_eq_lintegral_mul _ (measurable_puLe _) hm2]
    simp only [Pi.mul_apply]
    rw [lintegral_puLe isPU_rhoG hm2 fun γ hγ p hp => by rw [hθinv γ hγ p hp]]
    have hfin := lintegral_enorm_sq_lt_top_of_memLp hθm hθ2
    rw [muR, lintegral_withDensity_eq_lintegral_mul _ isPU_rhoG.1 hm2] at hfin
    simp only [Pi.mul_apply] at hfin
    refine ENNReal.mul_lt_top ?_ hfin
    have : ENat.card (Gam3 ⧸ (H' j).subgroupOf Gam3) < ⊤ := ENat.card_lt_top_of_finite
    exact_mod_cast this
  -- the combination
  have hDm : Measurable D := Finset.measurable_sum _ fun j _ => measurable_const.mul (hTm j)
  have hDaut : IsAut H (fun g => kub ↑g) D := by
    intro γ hγ p hp
    simp only [hDdef]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show θt (actP (g j) (slAct γ p)) = kub ↑γ * θt (actP (g j) p) from hTaut j γ hγ p hp]
    ring
  have hD2 : MemLp D 2 (muR ρH) := memLp_finsetSum _ fun j _ => (hT2 j).const_mul (c j)
  have hDinvn : ∀ γ ∈ H, ∀ p ∈ UHS, ‖D (slAct γ p)‖ = ‖D p‖ := by
    intro γ hγ p hp
    rw [hDaut γ hγ p hp, norm_mul, isUChar_kub.norm_eq γ (hH hγ), one_mul]
  -- the pairing of each translate with `D` vanishes
  have hTD : ∀ i, Integrable (fun p => conj (θt (actP (g i) p)) * D p) (muR ρH) := by
    intro i
    have h1 : MemLp (fun p => conj (θt (actP (g i) p))) 2 (muR ρH) :=
      (hT2 i).of_le ((Complex.continuous_conj.measurable.comp (hTm i)).aestronglyMeasurable)
        (Eventually.of_forall fun p => by rw [Complex.norm_conj])
    exact h1.integrable_mul hD2
  have hstep : ∀ i, ∫ p, conj (θt (actP (g i) p)) * D p ∂(muR ρH) = 0 := by
    intro i
    rw [integral_conj_comp_actP_mul (hH' i) (hg i) (e i) (he i) (hκ i) hρH hθm hθaut hDm hDaut
      (hTD i).2]
    have hDi : Measurable fun p => D (actP (g i)⁻¹ p) := hDm.comp (measurable_actP _)
    have hDiaut := isAut_comp_actP_inv (hg i) (e i) (he i) (hκ i) hDaut
    have hTrm : Measurable (trK (H' i) fun p => D (actP (g i)⁻¹ p)) := measurable_trK hDi
    have hTraut : IsAut Gam3 (fun g => kub ↑g) (trK (H' i) fun p => D (actP (g i)⁻¹ p)) :=
      isAut_trK hDiaut
    have hTr2 : MemLp (trK (H' i) fun p => D (actP (g i)⁻¹ p)) 2 (muR rhoG) := by
      have := Fintype.ofFinite (Gam3 ⧸ (H' i).subgroupOf Gam3)
      have hm2 : Measurable fun p => ‖D (actP (g i)⁻¹ p)‖ₑ ^ 2 := hDi.enorm.pow_const 2
      have hinv2 : ∀ γ ∈ H' i, ∀ p ∈ UHS,
          ‖D (actP (g i)⁻¹ (slAct γ p))‖ₑ ^ 2 = ‖D (actP (g i)⁻¹ p)‖ₑ ^ 2 := by
        intro γ hγ p hp
        have h := hDiaut γ hγ p hp
        simp only at h
        rw [h, enorm_mul]
        have h1 : ‖kub ↑γ‖ₑ = 1 := by
          rw [← ofReal_norm, isUChar_kub.norm_eq γ (hH' i hγ), ENNReal.ofReal_one]
        rw [h1, one_mul]
      have hbound : ∫⁻ p, ‖D (actP (g i)⁻¹ p)‖ₑ ^ 2 ∂(muR (puLe Gam3 (H' i) rhoG)) < ⊤ := by
        rw [lintegral_puLe_eq_comp_actP (hH' i) (hg i) (e i) (he i) hρH hm2 hinv2]
        have e2 : ∫⁻ p, ‖D (actP (g i)⁻¹ (actP (g i) p))‖ₑ ^ 2 ∂(muR ρH) =
            ∫⁻ p, ‖D p‖ₑ ^ 2 ∂(muR ρH) := by
          refine lintegral_congr_ae ?_
          filter_upwards [ae_muR_UHS ρH] with p hp
          rw [actP_inv_actP (hg i) hp]
        rw [e2]
        exact lintegral_enorm_sq_lt_top_of_memLp hDm hD2
      unfold trK
      simp_rw [tsum_fintype]
      refine memLp_finsetSum _ fun q _ => ?_
      refine MemLp.const_mul ?_ _
      refine memLp_two_of_lintegral (hDi.comp (measurable_slAct _)) ?_
      exact lt_of_le_of_lt (lintegral_slAct_inv_le_puLe q hm2) hbound
    have hz := inner_thetaL_eq_zero_of_const r hY hTrm hTraut hTr2 (h0 i)
    rw [L2.inner_def] at hz
    rw [← hz]
    refine integral_congr_ae ?_
    filter_upwards [thetaL_ae_eq_thetaF hr hY, hTr2.coeFn_toLp] with p h1 h2
    rw [RCLike.inner_apply', h1, h2]
  -- so `∫|D|² dν_H = 0`
  have hsq : ∫ p, ((‖D p‖ ^ 2 : ℝ) : ℂ) ∂(muR ρH) = 0 := by
    have e1 : ∀ p, ((‖D p‖ ^ 2 : ℝ) : ℂ) = ∑ i, conj (c i) * (conj (θt (actP (g i) p)) * D p) := by
      intro p
      rw [Complex.ofReal_pow, ← Complex.conj_mul']
      simp only [hDdef, map_sum, map_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    simp_rw [e1]
    rw [integral_finsetSum _ fun i _ => (hTD i).const_mul _]
    exact Finset.sum_eq_zero fun i _ => by rw [integral_const_mul, hstep i, mul_zero]
  have hsq' : ∫ p, ‖D p‖ ^ 2 ∂(muR ρH) = 0 := by
    have := hsq
    rw [integral_complex_ofReal] at this
    exact_mod_cast this
  have hDae : ∀ᵐ p ∂(muR ρH), D p = 0 := by
    have hi : Integrable (fun p => ‖D p‖ ^ 2) (muR ρH) := hD2.integrable_norm_pow two_ne_zero
    have := (integral_eq_zero_iff_of_nonneg (fun p => sq_nonneg ‖D p‖) hi).1 hsq'
    filter_upwards [this] with p hp
    have : ‖D p‖ ^ 2 = 0 := hp
    exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 this)
  exact ae_eq_zero_of_isPU hρH hDm hDinvn hDae

end Eis

end

#print axioms Eis.actP_one
#print axioms Eis.det_inv_eq_one
#print axioms Eis.actP_inv_actP
#print axioms Eis.actP_actP_inv
#print axioms Eis.lintegral_muR_actP
#print axioms Eis.integral_muR_actP
#print axioms Eis.integral_muR_slAct
#print axioms Eis.lintegral_muR_slAct
#print axioms Eis.isPU_comp_actP_inv
#print axioms Eis.integral_isPU_eq
#print axioms Eis.rhoG_lt_top
#print axioms Eis.measurable_puLe
#print axioms Eis.rhoG_slAct_le_puLe
#print axioms Eis.integral_puLe_eq
#print axioms Eis.measurable_trK
#print axioms Eis.isAut_trK
#print axioms Eis.isAut_comp_actP
#print axioms Eis.isAut_comp_actP_inv
#print axioms Eis.integral_conj_comp_actP_mul
#print axioms Eis.lintegral_puLe_eq_comp_actP
#print axioms Eis.lintegral_slAct_inv_le_puLe
#print axioms Eis.ae_eq_zero_of_isPU
#print axioms Eis.translates_eq_zero
