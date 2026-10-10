import KubotaSiegel

/-! # Integrals over `Γ\H³`, and unfolding (round 386)

S5f-8 of round 360's plan, part 4 (S5f-8c, part 2). Round 385 gave a measurable partition of unity `ρ` for
`SL_2(ℤ[ω])`. This file defines partitions of unity for every subgroup `Γ`. It proves that `∫ρ·F dz dv/v³` does
not depend on the choice, for `F` invariant under `Γ`. It also proves the unfolding over `H\Γ` for `H ≤ Γ`, with
an explicit partition of unity for the stabilizer `B_∞` of the cusp `∞`.

* **Partitions of unity** (`IsPU`, a definition; `isPU_top` and `IsPU.tsum_inv`, with `lintegral_slAct`,
  `ae_UHS`, `slAct_inv_slAct` and `slAct_slAct_inv`): `IsPU Γ ρ` says that `ρ` is measurable and
  `Σ_{γ∈Γ} ρ(γ·p) = 1` for `v > 0`. Round 385's `ρ` is one for the whole group.
* **Unfolding** (**`lintegral_unfold`**): `∫ρ·Σ_{γ∈Γ} Φ_γ dz dv/v³ = ∫Ψ dz dv/v³` when `Φ_γ(γ⁻¹·q) = Ψ(q)`
  for `v > 0`.
* **Independence** (**`lintegral_isPU_eq`**): `∫ρF = ∫ρ′F` for partitions of unity `ρ, ρ′` for `Γ` and `F`
  invariant under `Γ`.
* **Subgroups** (`outMul` and `puLe`, definitions, and the instance `countable_quot`; **`isPU_puLe`**, with
  `outMul_apply` and `isPU_puLe_top`; **`lintegral_puLe`**; **`lintegral_puLe_top_lt_top`**): for `Γ′ ≤ Γ`,
  `Σ_{q∈Γ/Γ′} ρ(q·p)` is a partition of unity for `Γ′`, and with it `∫ρ′F = #(Γ/Γ′)·∫ρF`. For `Γ` of finite
  index in `SL_2(ℤ[ω])`, `∫ρ_Γ dz dv/v³ < ∞`.
* **Folding** (**`tsum_fold`**): for `f` invariant under `H ≤ Γ` and a partition of unity `ρ_H` for `H`,
  `Σ_{γ∈Γ} ρ_H(γ·p)f(γ·p) = Σ_{q∈Γ/H} f(q⁻¹·p)`, a sum over the cosets `Hq⁻¹` of `H\Γ`.
* **Unfolding over `H\Γ`** (**`lintegral_unfold_cosets`**): `∫ρ·F·Σ_{q∈Γ/H} f(q⁻¹·) = ∫ρ_H·F·f`.
* **The cusp `∞`** (`bInf`, `bInfEquiv` and `rhoInf`, definitions; **`isPU_rhoInf`**, with `mem_bInf`,
  `bInf_det`, `slAct_bInf` and `tsum_fundP`; **`lintegral_rhoInf`**): the upper triangular elements act by
  `(z, v) ↦ (a²z + ab, v)`, and `ρ_∞(z, v) = 1_P(z)/#ℤ[ω]ˣ` is a partition of unity for them. Then
  `∫ρ_∞G dz dv/v³ = (1/#ℤ[ω]ˣ)·∫_{P×(0,∞)} G v⁻³ dz dv`.
-/

open MeasureTheory Set Module Filter NumberField Ideal PlanePoisson
open scoped ENNReal ComplexConjugate MatrixGroups

noncomputable section

namespace Eis

theorem lintegral_slAct (γ : SL(2, 𝓞 K)) {F : ℂ × ℝ → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ p, F (slAct γ p) ∂uhsMeasure = ∫⁻ p, F p ∂uhsMeasure :=
  lintegral_actP (det_map_σO γ.2) hF

theorem ae_UHS : ∀ᵐ p ∂uhsMeasure, p ∈ UHS :=
  withDensity_absolutelyContinuous _ _ (ae_restrict_mem measurableSet_UHS)

theorem slAct_inv_slAct (γ : SL(2, 𝓞 K)) {p : ℂ × ℝ} (hp : p ∈ UHS) :
    slAct γ⁻¹ (slAct γ p) = p := by
  rw [← slAct_mul _ _ hp, inv_mul_cancel, slAct_one]

theorem slAct_slAct_inv (γ : SL(2, 𝓞 K)) {p : ℂ × ℝ} (hp : p ∈ UHS) :
    slAct γ (slAct γ⁻¹ p) = p := by
  rw [← slAct_mul _ _ hp, mul_inv_cancel, slAct_one]

/-- **A partition of unity for `Γ`**: measurable, with `Σ_{γ∈Γ} ρ(γ·p) = 1` on upper half-space. -/
def IsPU (Γ : Subgroup SL(2, 𝓞 K)) (ρ : ℂ × ℝ → ℝ≥0∞) : Prop :=
  Measurable ρ ∧ ∀ p ∈ UHS, ∑' γ : Γ, ρ (slAct γ p) = 1

/-- Round 385's `ρ` is a partition of unity for the whole group. -/
theorem isPU_top : IsPU ⊤ rhoK := by
  refine ⟨measurable_rhoK, fun p hp => ?_⟩
  rw [← tsum_rhoK hp]
  exact (Equiv.subtypeUnivEquiv Subgroup.mem_top).tsum_eq (fun γ => rhoK (slAct γ p))

/-- `Σ_{γ∈Γ} ρ(γ⁻¹·p) = 1` as well. -/
theorem IsPU.tsum_inv {Γ : Subgroup SL(2, 𝓞 K)} {ρ : ℂ × ℝ → ℝ≥0∞} (hρ : IsPU Γ ρ) {p : ℂ × ℝ}
    (hp : p ∈ UHS) : ∑' γ : Γ, ρ (slAct (γ⁻¹ : Γ) p) = 1 := by
  rw [← hρ.2 p hp]
  exact (Equiv.inv Γ).tsum_eq (fun γ => ρ (slAct γ p))

/-- **Unfolding**: `∫ρ·Σ_{γ∈Γ} Φ_γ = ∫Ψ` when `Φ_γ(γ⁻¹·q) = Ψ(q)`. -/
theorem lintegral_unfold {Γ : Subgroup SL(2, 𝓞 K)} {ρ : ℂ × ℝ → ℝ≥0∞} (hρ : IsPU Γ ρ)
    {Φ : Γ → ℂ × ℝ → ℝ≥0∞} {Ψ : ℂ × ℝ → ℝ≥0∞} (hΦ : ∀ γ, Measurable (Φ γ)) (hΨ : Measurable Ψ)
    (h : ∀ γ : Γ, ∀ q ∈ UHS, Φ γ (slAct (γ⁻¹ : Γ) q) = Ψ q) :
    ∫⁻ p, ρ p * ∑' γ, Φ γ p ∂uhsMeasure = ∫⁻ q, Ψ q ∂uhsMeasure := by
  have h1 : ∀ γ : Γ, ∫⁻ p, ρ p * Φ γ p ∂uhsMeasure =
      ∫⁻ q, ρ (slAct (γ⁻¹ : Γ) q) * Ψ q ∂uhsMeasure := by
    intro γ
    rw [← lintegral_slAct (γ⁻¹ : Γ) (F := fun p => ρ p * Φ γ p) (hρ.1.mul (hΦ γ))]
    refine lintegral_congr_ae ?_
    filter_upwards [ae_UHS] with q hq
    rw [h γ q hq]
  calc ∫⁻ p, ρ p * ∑' γ, Φ γ p ∂uhsMeasure = ∫⁻ p, ∑' γ, ρ p * Φ γ p ∂uhsMeasure := by
        simp_rw [ENNReal.tsum_mul_left]
    _ = ∑' γ, ∫⁻ p, ρ p * Φ γ p ∂uhsMeasure :=
        lintegral_tsum fun γ => (hρ.1.mul (hΦ γ)).aemeasurable
    _ = ∑' γ : Γ, ∫⁻ q, ρ (slAct (γ⁻¹ : Γ) q) * Ψ q ∂uhsMeasure := tsum_congr h1
    _ = ∫⁻ q, ∑' γ : Γ, ρ (slAct (γ⁻¹ : Γ) q) * Ψ q ∂uhsMeasure :=
        (lintegral_tsum fun γ => ((hρ.1.comp (measurable_slAct _)).mul hΨ).aemeasurable).symm
    _ = ∫⁻ q, Ψ q ∂uhsMeasure := by
        refine lintegral_congr_ae ?_
        filter_upwards [ae_UHS] with q hq
        rw [ENNReal.tsum_mul_right, hρ.tsum_inv hq, one_mul]

/-- **The integral over `Γ\H³` does not depend on the partition of unity.** -/
theorem lintegral_isPU_eq {Γ : Subgroup SL(2, 𝓞 K)} {ρ ρ' : ℂ × ℝ → ℝ≥0∞} (hρ : IsPU Γ ρ)
    (hρ' : IsPU Γ ρ') {F : ℂ × ℝ → ℝ≥0∞} (hF : Measurable F)
    (hinv : ∀ γ ∈ Γ, ∀ p ∈ UHS, F (slAct γ p) = F p) :
    ∫⁻ p, ρ p * F p ∂uhsMeasure = ∫⁻ p, ρ' p * F p ∂uhsMeasure := by
  have e : ∫⁻ p, ρ p * F p ∂uhsMeasure =
      ∫⁻ p, ρ p * ∑' γ : Γ, ρ' (slAct γ p) * F p ∂uhsMeasure := by
    refine lintegral_congr_ae ?_
    filter_upwards [ae_UHS] with p hp
    rw [ENNReal.tsum_mul_right, hρ'.2 p hp, one_mul]
  rw [e]
  refine lintegral_unfold hρ (fun γ => (hρ'.1.comp (measurable_slAct _)).mul hF) (hρ'.1.mul hF)
    fun γ q hq => ?_
  rw [Subgroup.coe_inv, slAct_slAct_inv _ hq, hinv _ (Γ.inv_mem γ.2) q hq]

/-- `(q, h) ↦ q.out·h`, a bijection `(α ⧸ s) × s ≃ α`. -/
def outMul {α : Type*} [Group α] (s : Subgroup α) : (α ⧸ s) × s ≃ α :=
  Equiv.ofBijective (fun x => x.1.out * x.2)
    ⟨fun x y hxy => by
      have h1 : x.1 = y.1 := by
        have := congrArg (QuotientGroup.mk (s := s)) hxy
        simp only [QuotientGroup.mk_mul_of_mem _ x.2.2, QuotientGroup.mk_mul_of_mem _ y.2.2,
          QuotientGroup.out_eq'] at this
        exact this
      have hxy' : y.1.out * (x.2 : α) = y.1.out * y.2 := by simpa only [h1] using hxy
      exact Prod.ext h1 (Subtype.ext (mul_left_cancel hxy')),
    fun g => by
      obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul s g
      exact ⟨(QuotientGroup.mk g, h⁻¹), by simp [hh]⟩⟩

instance countable_quot (Γ : Subgroup SL(2, 𝓞 K)) (H : Subgroup Γ) : Countable (Γ ⧸ H) :=
  QuotientGroup.mk_surjective.countable

theorem outMul_apply {α : Type*} [Group α] (s : Subgroup α) (x : (α ⧸ s) × s) :
    outMul s x = x.1.out * x.2 := rfl

/-- **A partition of unity for a subgroup** `Γ′ ≤ Γ`: `Σ_{q∈Γ/Γ′} ρ(q·p)`. -/
def puLe (Γ Γ' : Subgroup SL(2, 𝓞 K)) (ρ : ℂ × ℝ → ℝ≥0∞) (p : ℂ × ℝ) : ℝ≥0∞ :=
  ∑' q : Γ ⧸ Γ'.subgroupOf Γ, ρ (slAct (q.out : SL(2, 𝓞 K)) p)

theorem isPU_puLe {Γ Γ' : Subgroup SL(2, 𝓞 K)} (hle : Γ' ≤ Γ) {ρ : ℂ × ℝ → ℝ≥0∞}
    (hρ : IsPU Γ ρ) : IsPU Γ' (puLe Γ Γ' ρ) := by
  refine ⟨Measurable.tsum fun q => hρ.1.comp (measurable_slAct _), fun p hp => ?_⟩
  unfold puLe
  rw [← hρ.2 p hp]
  calc ∑' γ' : Γ', ∑' q : Γ ⧸ Γ'.subgroupOf Γ, ρ (slAct (q.out : SL(2, 𝓞 K)) (slAct γ' p))
      = ∑' c : Γ'.subgroupOf Γ, ∑' q : Γ ⧸ Γ'.subgroupOf Γ,
          ρ (slAct ((q.out * c : Γ) : SL(2, 𝓞 K)) p) := by
        rw [← (Subgroup.subgroupOfEquivOfLe hle).toEquiv.tsum_eq]
        refine tsum_congr fun c => tsum_congr fun q => ?_
        rw [Subgroup.coe_mul, slAct_mul _ _ hp]
        rfl
    _ = ∑' q : Γ ⧸ Γ'.subgroupOf Γ, ∑' c : Γ'.subgroupOf Γ,
          ρ (slAct ((q.out * c : Γ) : SL(2, 𝓞 K)) p) := ENNReal.tsum_comm
    _ = ∑' x : (Γ ⧸ Γ'.subgroupOf Γ) × Γ'.subgroupOf Γ,
          ρ (slAct ((x.1.out * x.2 : Γ) : SL(2, 𝓞 K)) p) := ENNReal.tsum_prod.symm
    _ = ∑' γ : Γ, ρ (slAct (γ : SL(2, 𝓞 K)) p) :=
        (outMul _).tsum_eq (fun γ : Γ => ρ (slAct (γ : SL(2, 𝓞 K)) p))

/-- Every subgroup has a partition of unity: `Σ_{q ∈ SL_2(ℤ[ω])/Γ} ρ(q·p)`, from round 385's `ρ`. -/
theorem isPU_puLe_top (Γ : Subgroup SL(2, 𝓞 K)) : IsPU Γ (puLe ⊤ Γ rhoK) :=
  isPU_puLe le_top isPU_top

/-- **Folding**: for `f` invariant under `H ≤ Γ`, and `ρ` a partition of unity for `H`,
`Σ_{γ∈Γ} ρ(γ·p)f(γ·p) = Σ_{q∈Γ/H} f(q⁻¹·p)`, a sum over the cosets `Hq⁻¹` of `H\Γ`. -/
theorem tsum_fold {Γ H : Subgroup SL(2, 𝓞 K)} (hle : H ≤ Γ) {ρ : ℂ × ℝ → ℝ≥0∞} (hρ : IsPU H ρ)
    {f : ℂ × ℝ → ℝ≥0∞} (hf : ∀ h ∈ H, ∀ p ∈ UHS, f (slAct h p) = f p) {p : ℂ × ℝ}
    (hp : p ∈ UHS) :
    ∑' γ : Γ, ρ (slAct γ p) * f (slAct γ p) =
      ∑' q : Γ ⧸ H.subgroupOf Γ, f (slAct (q.out : SL(2, 𝓞 K))⁻¹ p) := by
  calc ∑' γ : Γ, ρ (slAct γ p) * f (slAct γ p)
      = ∑' x : (Γ ⧸ H.subgroupOf Γ) × H.subgroupOf Γ,
          ρ (slAct (((x.1.out * x.2)⁻¹ : Γ) : SL(2, 𝓞 K)) p) *
            f (slAct (((x.1.out * x.2)⁻¹ : Γ) : SL(2, 𝓞 K)) p) :=
        (((outMul _).trans (Equiv.inv Γ)).tsum_eq
          (fun γ : Γ => ρ (slAct (γ : SL(2, 𝓞 K)) p) * f (slAct (γ : SL(2, 𝓞 K)) p))).symm
    _ = ∑' q : Γ ⧸ H.subgroupOf Γ, ∑' c : H.subgroupOf Γ,
          ρ (slAct (((q.out * c)⁻¹ : Γ) : SL(2, 𝓞 K)) p) *
            f (slAct (((q.out * c)⁻¹ : Γ) : SL(2, 𝓞 K)) p) :=
        ENNReal.tsum_prod (f := fun (q : Γ ⧸ H.subgroupOf Γ) (c : H.subgroupOf Γ) =>
          ρ (slAct (((q.out * c)⁻¹ : Γ) : SL(2, 𝓞 K)) p) *
            f (slAct (((q.out * c)⁻¹ : Γ) : SL(2, 𝓞 K)) p))
    _ = ∑' q : Γ ⧸ H.subgroupOf Γ, ∑' c : H.subgroupOf Γ,
          ρ (slAct ((c : Γ) : SL(2, 𝓞 K))⁻¹ (slAct (q.out : SL(2, 𝓞 K))⁻¹ p)) *
            f (slAct (q.out : SL(2, 𝓞 K))⁻¹ p) := by
        refine tsum_congr fun q => tsum_congr fun c => ?_
        have hq : slAct (q.out : SL(2, 𝓞 K))⁻¹ p ∈ UHS := slAct_mem _ hp
        have e : slAct (((q.out * c)⁻¹ : Γ) : SL(2, 𝓞 K)) p =
            slAct ((c : Γ) : SL(2, 𝓞 K))⁻¹ (slAct (q.out : SL(2, 𝓞 K))⁻¹ p) := by
          rw [Subgroup.coe_inv, Subgroup.coe_mul, mul_inv_rev, slAct_mul _ _ hp]
        rw [e, hf _ (H.inv_mem (Subgroup.mem_subgroupOf.mp c.2)) _ hq]
    _ = ∑' q : Γ ⧸ H.subgroupOf Γ, f (slAct (q.out : SL(2, 𝓞 K))⁻¹ p) := by
        refine tsum_congr fun q => ?_
        have hq : slAct (q.out : SL(2, 𝓞 K))⁻¹ p ∈ UHS := slAct_mem _ hp
        have h1 : ∑' c : H.subgroupOf Γ,
            ρ (slAct ((c : Γ) : SL(2, 𝓞 K))⁻¹ (slAct (q.out : SL(2, 𝓞 K))⁻¹ p)) = 1 := by
          rw [← hρ.tsum_inv hq]
          exact (Subgroup.subgroupOfEquivOfLe hle).toEquiv.tsum_eq
            (fun h : H => ρ (slAct ((h⁻¹ : H) : SL(2, 𝓞 K)) (slAct (q.out : SL(2, 𝓞 K))⁻¹ p)))
        rw [ENNReal.tsum_mul_right, h1, one_mul]

/-- **The index**: `∫ρ′F = [Γ : Γ′]·∫ρF` for `ρ′ = Σ_{q∈Γ/Γ′} ρ(q·)` and `F` invariant under `Γ`. -/
theorem lintegral_puLe {Γ Γ' : Subgroup SL(2, 𝓞 K)} {ρ : ℂ × ℝ → ℝ≥0∞} (hρ : IsPU Γ ρ)
    {F : ℂ × ℝ → ℝ≥0∞} (hF : Measurable F) (hinv : ∀ γ ∈ Γ, ∀ p ∈ UHS, F (slAct γ p) = F p) :
    ∫⁻ p, puLe Γ Γ' ρ p * F p ∂uhsMeasure =
      ENat.card (Γ ⧸ Γ'.subgroupOf Γ) * ∫⁻ p, ρ p * F p ∂uhsMeasure := by
  have h1 : ∀ q : Γ ⧸ Γ'.subgroupOf Γ, ∫⁻ p, ρ (slAct (q.out : SL(2, 𝓞 K)) p) * F p ∂uhsMeasure =
      ∫⁻ p, ρ p * F p ∂uhsMeasure := by
    intro q
    rw [← lintegral_slAct (q.out : SL(2, 𝓞 K)) (F := fun p => ρ p * F p) (hρ.1.mul hF)]
    refine lintegral_congr_ae ?_
    filter_upwards [ae_UHS] with p hp
    rw [hinv _ q.out.2 p hp]
  unfold puLe
  simp_rw [← ENNReal.tsum_mul_right]
  calc ∫⁻ p, ∑' q : Γ ⧸ Γ'.subgroupOf Γ, ρ (slAct (q.out : SL(2, 𝓞 K)) p) * F p ∂uhsMeasure
      = ∑' q : Γ ⧸ Γ'.subgroupOf Γ, ∫⁻ p, ρ (slAct (q.out : SL(2, 𝓞 K)) p) * F p ∂uhsMeasure :=
        lintegral_tsum fun q => ((hρ.1.comp (measurable_slAct _)).mul hF).aemeasurable
    _ = ∑' _q : Γ ⧸ Γ'.subgroupOf Γ, ∫⁻ p, ρ p * F p ∂uhsMeasure := tsum_congr h1
    _ = _ := ENNReal.tsum_const _

/-- **The stabilizer of the cusp `∞`**: the upper triangular elements of `SL_2(ℤ[ω])`. -/
def bInf : Subgroup SL(2, 𝓞 K) where
  carrier := {γ | γ 1 0 = 0}
  mul_mem' {a b} ha hb := by
    have ha' : (a : Matrix (Fin 2) (Fin 2) (𝓞 K)) 1 0 = 0 := ha
    have hb' : (b : Matrix (Fin 2) (Fin 2) (𝓞 K)) 1 0 = 0 := hb
    change ((a * b : SL(2, 𝓞 K)) : Matrix (Fin 2) (Fin 2) (𝓞 K)) 1 0 = 0
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, ha', hb']
    ring
  one_mem' := by
    change ((1 : SL(2, 𝓞 K)) : Matrix (Fin 2) (Fin 2) (𝓞 K)) 1 0 = 0
    simp
  inv_mem' {a} ha := by
    have ha' : (a : Matrix (Fin 2) (Fin 2) (𝓞 K)) 1 0 = 0 := ha
    change ((a⁻¹ : SL(2, 𝓞 K)) : Matrix (Fin 2) (Fin 2) (𝓞 K)) 1 0 = 0
    rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
    simp [ha']

theorem mem_bInf {γ : SL(2, 𝓞 K)} : γ ∈ bInf ↔ γ 1 0 = 0 := Iff.rfl

theorem bInf_det {γ : SL(2, 𝓞 K)} (hγ : γ ∈ bInf) : γ 0 0 * γ 1 1 = 1 := by
  have h := γ.2
  rw [Matrix.det_fin_two, show (γ : Matrix (Fin 2) (Fin 2) (𝓞 K)) 1 0 = 0 from hγ, mul_zero,
    sub_zero] at h
  exact h

/-- `B_∞` acts by `(z, v) ↦ (a²z + ab, v)`. -/
theorem slAct_bInf {γ : SL(2, 𝓞 K)} (hγ : γ ∈ bInf) (p : ℂ × ℝ) :
    slAct γ p = (σO (γ 0 0) ^ 2 * p.1 + σO (γ 0 0 * γ 0 1), p.2) := by
  have h1 := bInf_det hγ
  have hc : σO (γ 1 0) = 0 := by rw [show (γ : Matrix (Fin 2) (Fin 2) (𝓞 K)) 1 0 = 0 from hγ,
    map_zero]
  have h1' : σO (γ 0 0) * σO (γ 1 1) = 1 := by rw [← map_mul, h1, map_one]
  have hd : σO (γ 1 1) ≠ 0 := right_ne_zero_of_mul_eq_one h1'
  have hn : Complex.normSq (σO (γ 1 1)) = 1 := by
    rw [normSq_σO, Ideal.span_singleton_eq_top.2 (IsUnit.of_mul_eq_one_right _ h1),
      Ideal.absNorm_top, Nat.cast_one]
  refine Prod.ext ?_ ?_
  · change uhsZ (σO (γ 0 0)) (σO (γ 0 1)) (σO (γ 1 0)) (σO (γ 1 1)) p.1 p.2 = _
    unfold uhsZ uhsDen
    simp only [hc, zero_mul, zero_add, map_zero, mul_zero, add_zero]
    rw [hn]
    have hconj : conj (σO (γ 1 1)) = σO (γ 0 0) := by
      have := Complex.mul_conj (σO (γ 1 1))
      rw [hn, Complex.ofReal_one] at this
      linear_combination (-(conj (σO (γ 1 1)))) * h1' + σO (γ 0 0) * this
    simp only [Complex.ofReal_one, div_one, hconj, map_mul]
    ring
  · change p.2 / uhsDen (σO (γ 1 0)) (σO (γ 1 1)) p.1 p.2 = p.2
    unfold uhsDen
    simp only [hc, zero_mul, zero_add, Complex.normSq_zero]
    rw [hn]
    simp

/-- `B_∞ ≃ ℤ[ω]ˣ × ℤ[ω]`: `(a, b; 0, a⁻¹) ↦ (a, ab)`. -/
def bInfEquiv : bInf ≃ (𝓞 K)ˣ × 𝓞 K where
  toFun γ := (⟨(γ : SL(2, 𝓞 K)) 0 0, (γ : SL(2, 𝓞 K)) 1 1, bInf_det γ.2,
      by rw [mul_comm]; exact bInf_det γ.2⟩, (γ : SL(2, 𝓞 K)) 0 0 * (γ : SL(2, 𝓞 K)) 0 1)
  invFun x := ⟨⟨!![(x.1 : 𝓞 K), ((x.1⁻¹ : (𝓞 K)ˣ) : 𝓞 K) * x.2; 0, ((x.1⁻¹ : (𝓞 K)ˣ) : 𝓞 K)],
      by simp [Matrix.det_fin_two]⟩, mem_bInf.2 rfl⟩
  left_inv γ := by
    have h1 := bInf_det γ.2
    apply Subtype.ext
    apply Subtype.ext
    have hγ : (γ : SL(2, 𝓞 K)) 1 0 = 0 := γ.2
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j
    · simp
    · simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.empty_val', Matrix.cons_val_fin_one, Fin.zero_eta, Fin.mk_one, Fin.isValue]
      change (γ : SL(2, 𝓞 K)) 1 1 * ((γ : SL(2, 𝓞 K)) 0 0 * (γ : SL(2, 𝓞 K)) 0 1) = _
      rw [← mul_assoc, mul_comm ((γ : SL(2, 𝓞 K)) 1 1), h1, one_mul]
    · simp [hγ]
    · simp
  right_inv x := by
    refine Prod.ext (Units.ext ?_) ?_
    · simp
    · simp [← mul_assoc]

/-- **Translates of `P`**: `Σ_{t∈ℤ[ω]} 1_P(w + σ(t)) = 1`. -/
theorem tsum_fundP (w : ℂ) : ∑' t : 𝓞 K, fundP.indicator (1 : ℂ → ℝ≥0∞) (w + σO t) = 1 := by
  obtain ⟨t₀, ht₀⟩ := exists_transl_mem_fundP w
  rw [tsum_eq_single t₀ fun t ht => ?_]
  · rw [Set.indicator_of_mem ht₀, Pi.one_apply]
  · refine Set.indicator_of_notMem (fun h => ht ?_) _
    have e : w + σO t₀ + σO (t - t₀) = w + σO t := by rw [map_sub]; ring
    have := eq_zero_of_mem_fundP ht₀ (by rw [e]; exact h)
    exact sub_eq_zero.1 this

/-- **The partition of unity for `B_∞`**: `ρ_∞(z, v) = 1_P(z)/#ℤ[ω]ˣ`. -/
def rhoInf (p : ℂ × ℝ) : ℝ≥0∞ := (Fintype.card (𝓞 K)ˣ : ℝ≥0∞)⁻¹ * fundP.indicator 1 p.1

theorem isPU_rhoInf : IsPU bInf rhoInf := by
  refine ⟨measurable_const.mul ((measurable_one.indicator measurableSet_fundP).comp measurable_fst),
    fun p _ => ?_⟩
  unfold rhoInf
  rw [ENNReal.tsum_mul_left]
  have h : ∑' γ : bInf, fundP.indicator (1 : ℂ → ℝ≥0∞) (slAct γ p).1 =
      Fintype.card (𝓞 K)ˣ := by
    calc ∑' γ : bInf, fundP.indicator (1 : ℂ → ℝ≥0∞) (slAct γ p).1
        = ∑' x : (𝓞 K)ˣ × 𝓞 K, fundP.indicator (1 : ℂ → ℝ≥0∞)
            (σO (x.1 : 𝓞 K) ^ 2 * p.1 + σO x.2) := by
          rw [← bInfEquiv.symm.tsum_eq]
          refine tsum_congr fun x => ?_
          rw [slAct_bInf (bInfEquiv.symm x).2]
          simp [bInfEquiv, ← mul_assoc]
      _ = ∑' u : (𝓞 K)ˣ, ∑' t : 𝓞 K, fundP.indicator (1 : ℂ → ℝ≥0∞)
            (σO (u : 𝓞 K) ^ 2 * p.1 + σO t) :=
          ENNReal.tsum_prod (f := fun (u : (𝓞 K)ˣ) (t : 𝓞 K) =>
            fundP.indicator (1 : ℂ → ℝ≥0∞) (σO (u : 𝓞 K) ^ 2 * p.1 + σO t))
      _ = ∑' _u : (𝓞 K)ˣ, (1 : ℝ≥0∞) := tsum_congr fun u => tsum_fundP _
      _ = Fintype.card (𝓞 K)ˣ := by rw [tsum_fintype, Finset.sum_const, Finset.card_univ]; simp
  rw [h]
  exact ENNReal.inv_mul_cancel (by simp) (by simp)

/-- **Unfolding over `H\Γ`**: `∫_{Γ\H³} F·Σ_{q∈Γ/H} f(q⁻¹·) = ∫_{H\H³} F·f`, for `F` invariant under `Γ` and
`f` invariant under `H ≤ Γ`, with any partitions of unity `ρ` for `Γ` and `ρ_H` for `H`. -/
theorem lintegral_unfold_cosets {Γ H : Subgroup SL(2, 𝓞 K)} (hle : H ≤ Γ) {ρ ρH : ℂ × ℝ → ℝ≥0∞}
    (hρ : IsPU Γ ρ) (hρH : IsPU H ρH) {F f : ℂ × ℝ → ℝ≥0∞} (hF : Measurable F) (hf : Measurable f)
    (hFinv : ∀ γ ∈ Γ, ∀ p ∈ UHS, F (slAct γ p) = F p)
    (hfinv : ∀ h ∈ H, ∀ p ∈ UHS, f (slAct h p) = f p) :
    ∫⁻ p, ρ p * (F p * ∑' q : Γ ⧸ H.subgroupOf Γ, f (slAct (q.out : SL(2, 𝓞 K))⁻¹ p))
      ∂uhsMeasure = ∫⁻ p, ρH p * (F p * f p) ∂uhsMeasure := by
  have e : ∫⁻ p, ρ p * (F p * ∑' q : Γ ⧸ H.subgroupOf Γ, f (slAct (q.out : SL(2, 𝓞 K))⁻¹ p))
      ∂uhsMeasure = ∫⁻ p, ρ p * ∑' γ : Γ, F p * (ρH (slAct γ p) * f (slAct γ p)) ∂uhsMeasure := by
    refine lintegral_congr_ae ?_
    filter_upwards [ae_UHS] with p hp
    rw [ENNReal.tsum_mul_left, tsum_fold hle hρH hfinv hp]
  rw [e]
  refine lintegral_unfold hρ
    (fun γ => hF.mul ((hρH.1.comp (measurable_slAct _)).mul (hf.comp (measurable_slAct _))))
    (hρH.1.mul (hF.mul hf)) fun γ q hq => ?_
  rw [Subgroup.coe_inv, slAct_slAct_inv _ hq, hFinv _ (Γ.inv_mem γ.2) q hq]
  ring

/-- **The integral over `B_∞\H³`**: `∫ρ_∞G dz dv/v³ = (1/#ℤ[ω]ˣ)·∫_{P×(0,∞)} G v⁻³ dz dv`. -/
theorem lintegral_rhoInf {G : ℂ × ℝ → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ p, rhoInf p * G p ∂uhsMeasure =
      (Fintype.card (𝓞 K)ˣ : ℝ≥0∞)⁻¹ * ∫⁻ p in fundP ×ˢ Ioi 0, G p * uhsW p := by
  have hm : Measurable fun p : ℂ × ℝ => fundP.indicator (1 : ℂ → ℝ≥0∞) p.1 :=
    (measurable_one.indicator measurableSet_fundP).comp measurable_fst
  have hP : MeasurableSet (Prod.fst ⁻¹' fundP : Set (ℂ × ℝ)) := measurable_fst measurableSet_fundP
  rw [lintegral_uhsMeasure (F := fun p => rhoInf p * G p) (isPU_rhoInf.1.mul hG)]
  unfold rhoInf
  simp_rw [mul_assoc]
  rw [lintegral_const_mul' _ _ (ENNReal.inv_ne_top.2 (by simp))]
  congr 1
  have e : ∀ p : ℂ × ℝ, fundP.indicator (1 : ℂ → ℝ≥0∞) p.1 * (G p * uhsW p) =
      (Prod.fst ⁻¹' fundP).indicator (fun p => G p * uhsW p) p := by
    intro p
    by_cases h : p.1 ∈ fundP
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem (show p ∈ Prod.fst ⁻¹' fundP from h),
        Pi.one_apply, one_mul]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (show p ∉ Prod.fst ⁻¹' fundP from h),
        zero_mul]
  simp_rw [e]
  rw [lintegral_indicator hP, Measure.restrict_restrict hP]
  congr 2

/-- **Finite volume for finite index**: `∫ρ_Γ dz dv/v³ < ∞` when `SL_2(ℤ[ω])/Γ` is finite, for
`ρ_Γ = Σ_{q∈SL_2(ℤ[ω])/Γ} ρ(q·)`. -/
theorem lintegral_puLe_top_lt_top (Γ : Subgroup SL(2, 𝓞 K))
    [Finite ((⊤ : Subgroup SL(2, 𝓞 K)) ⧸ Γ.subgroupOf ⊤)] :
    ∫⁻ p, puLe ⊤ Γ rhoK p ∂uhsMeasure < ⊤ := by
  have h := lintegral_puLe (Γ' := Γ) isPU_top (F := fun _ => 1) measurable_const
    fun _ _ _ _ => rfl
  simp only [mul_one] at h
  rw [h]
  exact ENNReal.mul_lt_top (ENat.toENNReal_lt_top.2 ENat.card_lt_top_of_finite)
    lintegral_rhoK_lt_top

end Eis

end

#print axioms Eis.lintegral_slAct
#print axioms Eis.ae_UHS
#print axioms Eis.slAct_inv_slAct
#print axioms Eis.slAct_slAct_inv
#print axioms Eis.isPU_top
#print axioms Eis.IsPU.tsum_inv
#print axioms Eis.lintegral_unfold
#print axioms Eis.lintegral_isPU_eq
#print axioms Eis.outMul_apply
#print axioms Eis.isPU_puLe
#print axioms Eis.isPU_puLe_top
#print axioms Eis.tsum_fold
#print axioms Eis.lintegral_puLe
#print axioms Eis.mem_bInf
#print axioms Eis.bInf_det
#print axioms Eis.slAct_bInf
#print axioms Eis.tsum_fundP
#print axioms Eis.isPU_rhoInf
#print axioms Eis.lintegral_unfold_cosets
#print axioms Eis.lintegral_rhoInf
#print axioms Eis.lintegral_puLe_top_lt_top
