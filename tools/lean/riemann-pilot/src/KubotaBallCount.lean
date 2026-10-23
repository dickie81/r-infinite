import KubotaBall

/-! # Counting the translates in a ball, and the Schur bound (round 420)

S5f-10 of round 360's plan, part 3 (S5f-10b, second half, first part). Round 418 replanned the residue on
the ball average `T_R`, and planned it on the quotient as an integral operator with kernel
`k(p, q) = Σ_γ χ(γ)·1[ppi(p, γq) ≤ R]`. This round proves the bounds that make that operator bounded, for
any subgroup `Γ` of `SL_2(ℤ[ω])` and any partition of unity `ρ` for it (round 386's `IsPU`), with
`ν = ρ dμ`.

* **The invariant under `SL_2(ℤ[ω])`** (**`mem_hball_slAct_iff`**, with `ppi_slAct`, `ppi_comm` and
  `measurable_ppi₂`): `γq ∈ B_R(p)` exactly when `γ⁻¹p ∈ B_R(q)`, by round 418's `pinv_actP` and the symmetry
  of `ppi`.
* **The counting function** (`cntB`, a definition; **`lintegral_cntB`** and **`cntB_comm`**, with
  `measurable_hball_ind`, `measurable_hball_ind_left`, `measurable_cntB`, `measurable_cntB_left` and
  `measurable_cntB_right`): `N(p, q) = #{γ ∈ Γ : γq ∈ B_R(p)}`, as a sum in `[0, ∞]`, is measurable on the
  product, `∫ρ(q)N(p, q) dμ(q) = μ(B_R(p))` by round 386's `lintegral_unfold`, and `N(p, q) = N(q, p)` on
  upper half-space.
* **The volume of a ball** (`VB`, a definition; **`uhsMeasure_hball`** and **`uhsMeasure_hball_lt_top`**):
  `μ(B_R(p)) = μ(B_R(0, 1)) = V_R` for every `p` in upper half-space (round 383's `measurePreserving_actP`),
  and `V_R < ∞` for `R ≥ 0` (round 418's `hball_one_subset`, where `v ≥ 1/(R + 2)`).
* **The Schur bound** (`muR`, a definition, and the instance `sFinite_muR`; **`lintegral_cntB_mul_le`**, with
  `ae_muR_UHS`, `lintegral_cntB_muR` and `lintegral_cntB_muR'`): `∫N(p, q) dν(q) = ∫N(q, p) dν(q) = V_R` for
  `p` in upper half-space, and `∫∫N(p, q)a(p)b(q) dν dν ≤ V_R·‖a‖₂‖b‖₂` for measurable `a, b ≥ 0`, by Hölder's
  inequality on `ν ⊗ ν` with density `N` (Mathlib's `ENNReal.lintegral_mul_le_Lp_mul_Lq`).
-/

open MeasureTheory Set Filter NumberField
open scoped ENNReal ComplexConjugate MatrixGroups

noncomputable section

namespace Eis

/-! ### The action and the point-pair invariant -/

theorem ppi_slAct (γ : SL(2, 𝓞 K)) {p q : ℂ × ℝ} (hp : p ∈ UHS) (hq : q ∈ UHS) :
    ppi (slAct γ p) (slAct γ q) = ppi p q :=
  pinv_actP (det_map_σO γ.2) p hp q hq

theorem ppi_comm (p q : ℂ × ℝ) : ppi p q = ppi q p := by
  unfold ppi; rw [← Complex.normSq_neg, neg_sub]; ring

/-- `γq ∈ B_R(p)` exactly when `γ⁻¹p ∈ B_R(q)`. -/
theorem mem_hball_slAct_iff (γ : SL(2, 𝓞 K)) {R : ℝ} {p q : ℂ × ℝ} (hp : p ∈ UHS)
    (hq : q ∈ UHS) : slAct γ q ∈ hball R p ↔ slAct γ⁻¹ p ∈ hball R q := by
  simp only [hball, mem_ofPred_eq, slAct_mem _ hp, slAct_mem _ hq, true_and]
  rw [← ppi_slAct γ⁻¹ hp (slAct_mem γ hq), slAct_inv_slAct γ hq, ppi_comm]

theorem measurable_ppi₂ : Measurable fun x : (ℂ × ℝ) × (ℂ × ℝ) => ppi x.1 x.2 := by
  unfold ppi; fun_prop

/-! ### The counting function -/

/-- `N(p, q) = #{γ ∈ Γ : γq ∈ B_R(p)}`. -/
def cntB (Γ : Subgroup SL(2, 𝓞 K)) (R : ℝ) (p q : ℂ × ℝ) : ℝ≥0∞ :=
  ∑' γ : Γ, (hball R p).indicator 1 (slAct γ q)

theorem measurable_hball_ind (R : ℝ) (γ : SL(2, 𝓞 K)) :
    Measurable fun x : (ℂ × ℝ) × (ℂ × ℝ) =>
      (hball R x.1).indicator (1 : ℂ × ℝ → ℝ≥0∞) (slAct γ x.2) := by
  set S : Set ((ℂ × ℝ) × (ℂ × ℝ)) := {x | slAct γ x.2 ∈ UHS ∧ ppi x.1 (slAct γ x.2) ≤ R} with hSdef
  have hS : MeasurableSet S :=
    (measurableSet_UHS.preimage ((measurable_slAct γ).comp measurable_snd)).inter
      (measurableSet_le (measurable_ppi₂.comp (measurable_fst.prodMk
        ((measurable_slAct γ).comp measurable_snd))) measurable_const)
  have e : (fun x : (ℂ × ℝ) × (ℂ × ℝ) => (hball R x.1).indicator (1 : ℂ × ℝ → ℝ≥0∞) (slAct γ x.2)) =
      S.indicator 1 := by
    funext x
    by_cases h : slAct γ x.2 ∈ hball R x.1
    · rw [indicator_of_mem h, indicator_of_mem (show x ∈ S from h)]; rfl
    · rw [indicator_of_notMem h, indicator_of_notMem (show x ∉ S from h)]
  rw [e]
  exact measurable_one.indicator hS

theorem measurable_cntB (Γ : Subgroup SL(2, 𝓞 K)) (R : ℝ) :
    Measurable fun x : (ℂ × ℝ) × (ℂ × ℝ) => cntB Γ R x.1 x.2 :=
  Measurable.tsum fun γ => measurable_hball_ind R γ

/-- **Unfolding**: `∫ρ(q)N(p, q) dμ(q) = μ(B_R(p))` (round 386's `lintegral_unfold`). -/
theorem lintegral_cntB {Γ : Subgroup SL(2, 𝓞 K)} {ρ : ℂ × ℝ → ℝ≥0∞} (hρ : IsPU Γ ρ) (R : ℝ)
    (p : ℂ × ℝ) : ∫⁻ q, ρ q * cntB Γ R p q ∂uhsMeasure = uhsMeasure (hball R p) := by
  rw [← lintegral_indicator_one (measurableSet_hball R p)]
  exact lintegral_unfold hρ (Φ := fun γ q => (hball R p).indicator 1 (slAct γ q))
    (Ψ := (hball R p).indicator 1)
    (fun γ => (measurable_one.indicator (measurableSet_hball R p)).comp (measurable_slAct _))
    (measurable_one.indicator (measurableSet_hball R p))
    (fun γ q hq => by simp only [Subgroup.coe_inv, slAct_slAct_inv _ hq])

/-- **Symmetry**: `N(p, q) = N(q, p)` on upper half-space. -/
theorem cntB_comm (Γ : Subgroup SL(2, 𝓞 K)) (R : ℝ) {p q : ℂ × ℝ} (hp : p ∈ UHS)
    (hq : q ∈ UHS) : cntB Γ R p q = cntB Γ R q p := by
  unfold cntB
  rw [← (Equiv.inv Γ).tsum_eq (fun γ : Γ => (hball R q).indicator 1 (slAct γ p))]
  refine tsum_congr fun γ => ?_
  have hiff := mem_hball_slAct_iff (γ : SL(2, 𝓞 K)) (R := R) hp hq
  simp only [Equiv.inv_apply, Subgroup.coe_inv]
  by_cases h : slAct γ q ∈ hball R p
  · rw [indicator_of_mem h, indicator_of_mem (hiff.1 h)]; rfl
  · rw [indicator_of_notMem h, indicator_of_notMem fun h' => h (hiff.2 h')]

/-! ### The volume of a ball -/

/-- `μ(B_R(p)) = μ(B_R(0, 1))` for `p` in upper half-space. -/
theorem uhsMeasure_hball (R : ℝ) {p : ℂ × ℝ} (hp : p ∈ UHS) :
    uhsMeasure (hball R p) = uhsMeasure (hball R (0, 1)) := by
  have hv : (0 : ℝ) < p.2 := hp
  set a : ℂ := ((Real.sqrt p.2 : ℝ) : ℂ) with ha
  have ha0 : a ≠ 0 := by
    rw [ha]; exact_mod_cast (Real.sqrt_pos.2 hv).ne'
  have hna : Complex.normSq a = p.2 := by
    rw [ha, Complex.normSq_ofReal, Real.mul_self_sqrt hv.le]
  set g : Matrix (Fin 2) (Fin 2) ℂ := !![1, p.1; 0, 1] * !![a, 0; 0, a⁻¹] with hgdef
  have hg : g.det = 1 := by rw [hgdef, Matrix.det_mul, det_transl, det_diag ha0, one_mul]
  have h01 : ((0 : ℂ), (1 : ℝ)) ∈ UHS := (zero_lt_one : (0 : ℝ) < 1)
  have hgp : actP g (0, 1) = p := by
    rw [hgdef, actP_mul (det_transl _) (det_diag ha0) h01]
    simp only [actP, uhsAct_diag ha0, uhsAct_transl, mul_zero, zero_add, hna, mul_one]
  rw [← hgp, ← (measurePreserving_actP hg).measure_preimage
    (measurableSet_hball R _).nullMeasurableSet]
  refine measure_congr ?_
  filter_upwards [ae_UHS] with q hq
  change (actP g q ∈ hball R (actP g (0, 1))) = (q ∈ hball R (0, 1))
  exact propext (mem_hball_actP hg h01 hq)

/-- `μ(B_R(0, 1)) < ∞`. -/
theorem uhsMeasure_hball_lt_top {R : ℝ} (hR : 0 ≤ R) : uhsMeasure (hball R (0, 1)) < ⊤ := by
  rw [uhsMeasure, withDensity_apply _ (measurableSet_hball R _)]
  refine lt_of_le_of_lt (setLIntegral_mono (g := fun _ => ENNReal.ofReal ((R + 2) ^ 3))
    measurable_const fun q hq => ?_) ?_
  · have hIcc := (Set.mem_prod.1 (hball_one_subset hR hq)).2
    have hv : 0 < q.2 := lt_of_lt_of_le (by positivity) hIcc.1
    unfold uhsW
    refine ENNReal.ofReal_le_ofReal ?_
    rw [zpow_neg, zpow_ofNat, inv_le_comm₀ (by positivity) (by positivity), ← inv_pow]
    refine pow_le_pow_left₀ (by positivity) ?_ 3
    have := hIcc.1
    rwa [one_div] at this
  · rw [setLIntegral_const, Measure.restrict_apply (measurableSet_hball R _)]
    refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (lt_of_le_of_lt (measure_mono inter_subset_left) (volume_hball_one_lt_top hR))

/-! ### The Schur bound -/

/-- The measure `ρ dμ`. -/
def muR (ρ : ℂ × ℝ → ℝ≥0∞) : Measure (ℂ × ℝ) := uhsMeasure.withDensity ρ

/-- `V_R = μ(B_R(0, 1))`, the volume of a ball. -/
def VB (R : ℝ) : ℝ≥0∞ := uhsMeasure (hball R (0, 1))

theorem ae_muR_UHS (ρ : ℂ × ℝ → ℝ≥0∞) : ∀ᵐ p ∂(muR ρ), p ∈ UHS :=
  withDensity_absolutelyContinuous _ _ ae_UHS

theorem measurable_cntB_left (Γ : Subgroup SL(2, 𝓞 K)) (R : ℝ) (p : ℂ × ℝ) :
    Measurable fun q => cntB Γ R p q := by
  unfold cntB
  exact Measurable.tsum fun γ =>
    (measurable_one.indicator (measurableSet_hball R p)).comp (measurable_slAct _)

theorem measurable_hball_ind_left (R : ℝ) (w : ℂ × ℝ) :
    Measurable fun p : ℂ × ℝ => (hball R p).indicator (1 : ℂ × ℝ → ℝ≥0∞) w := by
  set S : Set (ℂ × ℝ) := {p | w ∈ UHS ∧ ppi p w ≤ R} with hSdef
  have hpw : Measurable fun p : ℂ × ℝ => ppi p w := by
    have : (fun p : ℂ × ℝ => ppi p w) = fun p => ppi w p := funext fun p => ppi_comm p w
    rw [this]; exact measurable_ppi w
  have hS : MeasurableSet S := (MeasurableSet.const _).inter (measurableSet_le hpw measurable_const)
  have e : (fun p : ℂ × ℝ => (hball R p).indicator (1 : ℂ × ℝ → ℝ≥0∞) w) = S.indicator 1 := by
    funext p
    by_cases h : w ∈ hball R p
    · rw [indicator_of_mem h, indicator_of_mem (show p ∈ S from h)]; rfl
    · rw [indicator_of_notMem h, indicator_of_notMem (show p ∉ S from h)]
  rw [e]; exact measurable_one.indicator hS

theorem measurable_cntB_right (Γ : Subgroup SL(2, 𝓞 K)) (R : ℝ) (q : ℂ × ℝ) :
    Measurable fun p => cntB Γ R p q := by
  unfold cntB
  exact Measurable.tsum fun γ => measurable_hball_ind_left R (slAct (γ : SL(2, 𝓞 K)) q)

/-- `∫N(p, q) dν(q) = V_R` for `p` in upper half-space. -/
theorem lintegral_cntB_muR {Γ : Subgroup SL(2, 𝓞 K)} {ρ : ℂ × ℝ → ℝ≥0∞} (hρ : IsPU Γ ρ)
    (R : ℝ) {p : ℂ × ℝ} (hp : p ∈ UHS) : ∫⁻ q, cntB Γ R p q ∂(muR ρ) = VB R := by
  rw [muR, lintegral_withDensity_eq_lintegral_mul _ hρ.1 (measurable_cntB_left Γ R p)]
  simp only [Pi.mul_apply]
  rw [lintegral_cntB hρ R p, uhsMeasure_hball R hp, VB]

/-- `∫N(p, q) dν(p) = V_R` for `q` in upper half-space. -/
theorem lintegral_cntB_muR' {Γ : Subgroup SL(2, 𝓞 K)} {ρ : ℂ × ℝ → ℝ≥0∞} (hρ : IsPU Γ ρ)
    (R : ℝ) {q : ℂ × ℝ} (hq : q ∈ UHS) : ∫⁻ p, cntB Γ R p q ∂(muR ρ) = VB R := by
  rw [← lintegral_cntB_muR hρ R hq]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_muR_UHS ρ] with p hp
  exact cntB_comm Γ R hp hq

instance sFinite_muR (ρ : ℂ × ℝ → ℝ≥0∞) : SFinite (muR ρ) := by
  unfold muR uhsMeasure; infer_instance

/-- **The Schur bound**: `∫∫N(p, q)a(p)b(q) dν dν ≤ V_R·‖a‖₂‖b‖₂`. -/
theorem lintegral_cntB_mul_le {Γ : Subgroup SL(2, 𝓞 K)} {ρ : ℂ × ℝ → ℝ≥0∞} (hρ : IsPU Γ ρ)
    (R : ℝ) {a b : ℂ × ℝ → ℝ≥0∞} (ha : Measurable a) (hb : Measurable b) :
    ∫⁻ p, ∫⁻ q, cntB Γ R p q * a p * b q ∂(muR ρ) ∂(muR ρ) ≤
      VB R * ((∫⁻ p, a p ^ 2 ∂(muR ρ)) ^ (1 / 2 : ℝ) *
        (∫⁻ q, b q ^ 2 ∂(muR ρ)) ^ (1 / 2 : ℝ)) := by
  set ν := muR ρ with hν
  have hN := measurable_cntB Γ R
  set μ₂ := (ν.prod ν).withDensity (fun x => cntB Γ R x.1 x.2) with hμ₂
  have hA : Measurable fun x : (ℂ × ℝ) × (ℂ × ℝ) => a x.1 := ha.comp measurable_fst
  have hB : Measurable fun x : (ℂ × ℝ) × (ℂ × ℝ) => b x.2 := hb.comp measurable_snd
  have h1 : ∫⁻ p, ∫⁻ q, cntB Γ R p q * a p * b q ∂ν ∂ν =
      ∫⁻ x, ((fun x : (ℂ × ℝ) × (ℂ × ℝ) => a x.1) * fun x : (ℂ × ℝ) × (ℂ × ℝ) => b x.2) x ∂μ₂ := by
    rw [hμ₂, lintegral_withDensity_eq_lintegral_mul _ hN (hA.mul hB),
      lintegral_prod _ (hN.mul (hA.mul hB)).aemeasurable]
    refine lintegral_congr fun p => lintegral_congr fun q => ?_
    simp only [Pi.mul_apply]; ring
  have h2 := ENNReal.lintegral_mul_le_Lp_mul_Lq μ₂ Real.HolderConjugate.two_two hA.aemeasurable
    hB.aemeasurable
  have h3 : ∫⁻ x, a x.1 ^ (2 : ℝ) ∂μ₂ = VB R * ∫⁻ p, a p ^ 2 ∂ν := by
    simp only [ENNReal.rpow_two]
    rw [hμ₂, lintegral_withDensity_eq_lintegral_mul _ hN (hA.pow_const 2),
      lintegral_prod _ (hN.mul (hA.pow_const 2)).aemeasurable]
    calc ∫⁻ p, ∫⁻ q, ((fun x : (ℂ × ℝ) × (ℂ × ℝ) => cntB Γ R x.1 x.2) *
          fun x : (ℂ × ℝ) × (ℂ × ℝ) => a x.1 ^ 2) (p, q) ∂ν ∂ν
        = ∫⁻ p, (∫⁻ q, cntB Γ R p q ∂ν) * a p ^ 2 ∂ν := by
          refine lintegral_congr fun p => ?_
          simp only [Pi.mul_apply]
          rw [lintegral_mul_const _ (measurable_cntB_left Γ R p)]
      _ = ∫⁻ p, VB R * a p ^ 2 ∂ν := by
          refine lintegral_congr_ae ?_
          filter_upwards [ae_muR_UHS ρ] with p hp
          rw [lintegral_cntB_muR hρ R hp]
      _ = VB R * ∫⁻ p, a p ^ 2 ∂ν := lintegral_const_mul _ (ha.pow_const 2)
  have h4 : ∫⁻ x, b x.2 ^ (2 : ℝ) ∂μ₂ = VB R * ∫⁻ q, b q ^ 2 ∂ν := by
    simp only [ENNReal.rpow_two]
    rw [hμ₂, lintegral_withDensity_eq_lintegral_mul _ hN (hB.pow_const 2),
      lintegral_prod_symm _ (hN.mul (hB.pow_const 2)).aemeasurable]
    calc ∫⁻ q, ∫⁻ p, ((fun x : (ℂ × ℝ) × (ℂ × ℝ) => cntB Γ R x.1 x.2) *
          fun x : (ℂ × ℝ) × (ℂ × ℝ) => b x.2 ^ 2) (p, q) ∂ν ∂ν
        = ∫⁻ q, (∫⁻ p, cntB Γ R p q ∂ν) * b q ^ 2 ∂ν := by
          refine lintegral_congr fun q => ?_
          simp only [Pi.mul_apply]
          rw [lintegral_mul_const _ (measurable_cntB_right Γ R q)]
      _ = ∫⁻ q, VB R * b q ^ 2 ∂ν := by
          refine lintegral_congr_ae ?_
          filter_upwards [ae_muR_UHS ρ] with q hq
          rw [lintegral_cntB_muR' hρ R hq]
      _ = VB R * ∫⁻ q, b q ^ 2 ∂ν := lintegral_const_mul _ (hb.pow_const 2)
  rw [h1]
  refine h2.trans (le_of_eq ?_)
  rw [h3, h4, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2),
    ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  have hV : VB R ^ (1 / 2 : ℝ) * VB R ^ (1 / 2 : ℝ) = VB R := by
    rw [← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2), ← sq, ← ENNReal.rpow_two,
      ← ENNReal.rpow_mul]
    norm_num
  calc VB R ^ (1 / 2 : ℝ) * (∫⁻ p, a p ^ 2 ∂ν) ^ (1 / 2 : ℝ) *
        (VB R ^ (1 / 2 : ℝ) * (∫⁻ q, b q ^ 2 ∂ν) ^ (1 / 2 : ℝ))
      = (VB R ^ (1 / 2 : ℝ) * VB R ^ (1 / 2 : ℝ)) *
        ((∫⁻ p, a p ^ 2 ∂ν) ^ (1 / 2 : ℝ) * (∫⁻ q, b q ^ 2 ∂ν) ^ (1 / 2 : ℝ)) := by ring
    _ = _ := by rw [hV]

end Eis

end

#print axioms Eis.ppi_slAct
#print axioms Eis.ppi_comm
#print axioms Eis.mem_hball_slAct_iff
#print axioms Eis.measurable_ppi₂
#print axioms Eis.measurable_hball_ind
#print axioms Eis.measurable_cntB
#print axioms Eis.lintegral_cntB
#print axioms Eis.cntB_comm
#print axioms Eis.uhsMeasure_hball
#print axioms Eis.uhsMeasure_hball_lt_top
#print axioms Eis.ae_muR_UHS
#print axioms Eis.measurable_cntB_left
#print axioms Eis.measurable_hball_ind_left
#print axioms Eis.measurable_cntB_right
#print axioms Eis.lintegral_cntB_muR
#print axioms Eis.lintegral_cntB_muR'
#print axioms Eis.lintegral_cntB_mul_le
