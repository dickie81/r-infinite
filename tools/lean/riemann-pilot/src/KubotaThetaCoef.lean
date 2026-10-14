import KubotaPmTheta

/-! # The Fourier coefficients of θ (round 432)

S5f-10 of round 360's plan, part 15 (S5f-10f, fifth part). Round 431's next step planned the Fourier
coefficients of θ's automorphic representative `θ̃` (round 425's `thetaF`): `|θ̃|` integrable on
`3P × [α, β]`, the unfolding of `P_m(ψ)` against `θ̃`, and the coefficients for almost every `v`. This round
proves them, for `m = δ₃x`, `r > 0` and `Y > 0`:

* **Counting** (`rowBd`, `boxT`, `cBox`, `boxZ` and `cTr`, definitions; **`tsum_boxT_le`** and
  **`tsum_boxZ_le`**, with `rowBd_finite`, `row_mem_rowBd`, `measurableSet_boxT`, `cBox_ne_top`,
  `tsum_boxT_le_of_siegel`, `measurableSet_boxZ` and `cTr_ne_top`): for `α > 0`, the number of
  `γ ∈ SL_2(ℤ[ω])` with `γ·p` in the box `{|z| ≤ Z, α ≤ v ≤ β}` is bounded independently of `p`. For `p` in
  round 385's Siegel set the bottom rows of such `γ` lie in a finite set depending only on `α`, and two such
  `γ` with the same bottom row and `γ·p` in one translate of `P` coincide; every orbit meets the Siegel set
  (round 385's `exists_mem_siegelK`).
* **Local integrability** (the instance `isFiniteMeasure_muR_rhoG`; **`lintegral_boxZ_lt_top`** and
  **`lintegral_boxZ_thetaF_lt_top`**, with `measurable_thetaF`, `memLp_thetaF` and `enorm_thetaF_slAct`): a
  measurable function `u` with `|u|` invariant under `Γ_1(3)` and `∫|u| dν < ∞` is integrable on every such
  box (round 386's `lintegral_unfold`); `ν` is finite, so this applies to `θ̃`.
* **Unfolding** (**`inner_pmSer_thetaL_unfold`**, with `setLIntegral_volume_le` and
  `integral_fundP3_conj_mul_of_int`): for `ψ` measurable and bounded, vanishing outside `[α, β]` with `α > 0`,
  `⟨P_m(ψ), θ⟩ = ∫_0^∞ v^{−3}·conj ψ(v)·∫_{3P} ĕ(−mz/9)θ̃(z, v) dz dv`.
* **The coefficients** (**`coef_thetaF_ae`**, with `integrableOn_slice`, `integrableOn_ebr_thetaF` and
  `Ioi_zero_eq_iUnion_Icc`): for `x ≠ 0`, `∫_{3P} ĕ(−mz/9)θ̃(z, v) dz = ρ(m)·v·K_{1/3}(4π|m|v/9)` for almost
  every `v > 0`, from round 431's `⟨P_m(ψ), θ⟩ = ρ(m)·J_ψ(4/3)` with `ψ` the indicators of measurable subsets
  of `[1/(n + 1), n + 1]`.
-/

open MeasureTheory Set Filter NumberField Complex Ideal Asymptotics
open scoped ENNReal Topology MatrixGroups ComplexConjugate

noncomputable section

namespace Eis

/-! ### Counting the translates in a box -/

/-- The bottom rows that can send a point of the Siegel set to height `≥ α`. -/
def rowBd (α : ℝ) : Set (𝓞 K × 𝓞 K) :=
  {cd | Complex.normSq (σO cd.1) ≤ 2 / α ∧ ‖σO cd.2‖ ≤ 1 + 1 / α + 2 * Real.sqrt (2 / α)}

theorem rowBd_finite (α : ℝ) : (rowBd α).Finite := by
  refine ((finite_normSq_le (2 / α)).prod
    (finite_normSq_le ((1 + 1 / α + 2 * Real.sqrt (2 / α)) ^ 2))).subset ?_
  rintro ⟨c, d⟩ ⟨hc, hd⟩
  refine ⟨hc, ?_⟩
  show Complex.normSq (σO d) ≤ _
  rw [Complex.normSq_eq_norm_sq]
  exact pow_le_pow_left₀ (norm_nonneg _) hd 2

/-- **A bottom row sending a point of the Siegel set to height `≥ α` is in `rowBd α`.** -/
theorem row_mem_rowBd {α : ℝ} (hα : 0 < α) {s : ℂ × ℝ} (hs : s ∈ siegelK) (γ : SL(2, 𝓞 K))
    (hγ : α ≤ (slAct γ s).2) : (γ 1 0, γ 1 1) ∈ rowBd α := by
  have hv : 1 / 2 ≤ s.2 := hs.2
  have hv0 : 0 < s.2 := by linarith
  have hz : ‖s.1‖ ≤ 2 := norm_le_two_of_mem_fundP hs.1
  have hD := slDen_pos γ (siegelK_subset_UHS hs)
  rw [slAct_snd, le_div_iff₀ hD] at hγ
  unfold uhsDen at hγ
  have h1 := Complex.normSq_nonneg (σO (γ 1 0) * s.1 + σO (γ 1 1))
  have h2 := Complex.normSq_nonneg (σO (γ 1 0))
  have hcv : α * Complex.normSq (σO (γ 1 0)) * s.2 ≤ 1 := by
    have : α * (Complex.normSq (σO (γ 1 0)) * s.2 ^ 2) ≤ s.2 := by nlinarith
    nlinarith
  have hcb : Complex.normSq (σO (γ 1 0)) ≤ 2 / α := by
    rw [le_div_iff₀ hα]
    nlinarith
  refine ⟨hcb, ?_⟩
  have hsq : 0 ≤ Real.sqrt (2 / α) := Real.sqrt_nonneg _
  by_cases hc : γ 1 0 = 0
  · have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
      have := γ.2; rwa [Matrix.det_fin_two] at this
    rw [hc, mul_zero, sub_zero] at hdet
    have hu : IsUnit (γ 1 1) := IsUnit.of_mul_eq_one_right (γ 0 0) hdet
    have := norm_σO_unit hu.unit
    rw [IsUnit.unit_spec] at this
    rw [this]
    have : 0 ≤ 1 / α := by positivity
    linarith
  · have hc1 : 1 ≤ ‖σO (γ 1 0)‖ := one_le_norm_σO hc
    have hc1' : 1 ≤ Complex.normSq (σO (γ 1 0)) := by
      rw [Complex.normSq_eq_norm_sq]; nlinarith
    have hva : α * s.2 ≤ 1 := by nlinarith
    have hN : Complex.normSq (σO (γ 1 0) * s.1 + σO (γ 1 1)) ≤ (1 / α) ^ 2 := by
      have hN1 : α * Complex.normSq (σO (γ 1 0) * s.1 + σO (γ 1 1)) ≤ s.2 := by
        nlinarith [mul_nonneg hα.le (mul_nonneg h2 (sq_nonneg s.2))]
      rw [div_pow, one_pow, le_div_iff₀ (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_left hN1 hα.le]
    have e1 : ‖σO (γ 1 0) * s.1 + σO (γ 1 1)‖ ≤ 1 / α := by
      rw [Complex.normSq_eq_norm_sq] at hN
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hN
    have e2 : ‖σO (γ 1 0)‖ ≤ Real.sqrt (2 / α) := by
      rw [← Real.sqrt_sq (norm_nonneg (σO (γ 1 0))), ← Complex.normSq_eq_norm_sq]
      exact Real.sqrt_le_sqrt hcb
    calc ‖σO (γ 1 1)‖ = ‖(σO (γ 1 0) * s.1 + σO (γ 1 1)) - σO (γ 1 0) * s.1‖ := by ring_nf
      _ ≤ ‖σO (γ 1 0) * s.1 + σO (γ 1 1)‖ + ‖σO (γ 1 0) * s.1‖ := norm_sub_le _ _
      _ ≤ 1 / α + Real.sqrt (2 / α) * 2 := by
          rw [norm_mul]
          exact add_le_add e1 (mul_le_mul e2 hz (norm_nonneg _) hsq)
      _ ≤ 1 + 1 / α + 2 * Real.sqrt (2 / α) := by linarith

/-- The box `{(z, v) : z − σ(t) ∈ P, α ≤ v ≤ β}`. -/
def boxT (t : 𝓞 K) (α β : ℝ) : Set (ℂ × ℝ) := {p | p.1 - σO t ∈ fundP ∧ α ≤ p.2 ∧ p.2 ≤ β}

theorem measurableSet_boxT (t : 𝓞 K) (α β : ℝ) : MeasurableSet (boxT t α β) :=
  ((measurable_fst.sub measurable_const) measurableSet_fundP).inter
    ((measurableSet_le measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd measurable_const))

/-- The bound `#rowBd(α)`. -/
def cBox (α : ℝ) : ℝ≥0∞ := ∑' cd : 𝓞 K × 𝓞 K, (rowBd α).indicator 1 cd

theorem cBox_ne_top (α : ℝ) : cBox α ≠ ⊤ := by
  have hfin := rowBd_finite α
  unfold cBox
  rw [tsum_eq_sum (s := hfin.toFinset) fun cd hcd => ?_]
  · refine ENNReal.sum_ne_top.2 fun cd _ => ?_
    by_cases h : cd ∈ rowBd α
    · rw [Set.indicator_of_mem h]; simp
    · rw [Set.indicator_of_notMem h]; simp
  · rw [Set.Finite.mem_toFinset] at hcd
    exact Set.indicator_of_notMem hcd _

/-- **At most `#rowBd(α)` elements send a point of the Siegel set into a box**: two of them with the same
bottom row differ by a translation, which moves `P` off itself (round 385's `eq_zero_of_mem_fundP`). -/
theorem tsum_boxT_le_of_siegel (t : 𝓞 K) {α : ℝ} (hα : 0 < α) (β : ℝ) {s : ℂ × ℝ} (hs : s ∈ siegelK) :
    ∑' γ : SL(2, 𝓞 K), (boxT t α β).indicator 1 (slAct γ s) ≤ cBox α := by
  have hsU := siegelK_subset_UHS hs
  set S : Set SL(2, 𝓞 K) := {γ | slAct γ s ∈ boxT t α β} with hS
  have e1 : ∑' γ : SL(2, 𝓞 K), (boxT t α β).indicator 1 (slAct γ s) =
      ∑' γ : S, (1 : ℝ≥0∞) := by
    rw [tsum_subtype S (fun _ => (1 : ℝ≥0∞))]
    refine tsum_congr fun γ => ?_
    by_cases h : slAct γ s ∈ boxT t α β
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem (show γ ∈ S from h), Pi.one_apply]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (show γ ∉ S from h)]
  have e2 : ∑' γ : S, (1 : ℝ≥0∞) =
      ∑' γ : S, (rowBd α).indicator 1 ((γ : SL(2, 𝓞 K)) 1 0, (γ : SL(2, 𝓞 K)) 1 1) := by
    refine tsum_congr fun γ => ?_
    rw [Set.indicator_of_mem (row_mem_rowBd hα hs γ γ.2.2.1), Pi.one_apply]
  have hinj : Function.Injective fun γ : S => ((γ : SL(2, 𝓞 K)) 1 0, (γ : SL(2, 𝓞 K)) 1 1) := by
    rintro ⟨γ, hγ⟩ ⟨γ', hγ'⟩ heq
    simp only [Prod.mk.injEq] at heq
    have e := eq_slT_mul heq.1.symm heq.2.symm
    have h2 : slAct γ' s ∈ boxT t α β := hγ'
    rw [e, slAct_mul _ _ hsU, slAct_slT] at h2
    have h1 : (slAct γ s).1 - σO t ∈ fundP := hγ.1
    have h2' : (slAct γ s).1 - σO t + σO (γ 0 0 * γ' 0 1 - γ' 0 0 * γ 0 1) ∈ fundP := by
      have := h2.1
      simp only at this
      rwa [show (slAct γ s).1 + σO (γ 0 0 * γ' 0 1 - γ' 0 0 * γ 0 1) - σO t =
        (slAct γ s).1 - σO t + σO (γ 0 0 * γ' 0 1 - γ' 0 0 * γ 0 1) by ring] at this
    have ht := eq_zero_of_mem_fundP h1 h2'
    refine Subtype.ext ?_
    show γ = γ'
    rw [e, ht, slT_zero, one_mul]
  rw [e1, e2]
  exact ENNReal.tsum_comp_le_tsum_of_injective hinj _

/-- The same bound at every point of upper half-space, through a translate in the Siegel set (round
385's `exists_mem_siegelK`). -/
theorem tsum_boxT_le (t : 𝓞 K) {α : ℝ} (hα : 0 < α) (β : ℝ) {p : ℂ × ℝ} (hp : p ∈ UHS) :
    ∑' γ : SL(2, 𝓞 K), (boxT t α β).indicator 1 (slAct γ p) ≤ cBox α := by
  obtain ⟨g, hg⟩ := exists_mem_siegelK hp
  calc ∑' γ : SL(2, 𝓞 K), (boxT t α β).indicator 1 (slAct γ p)
      = ∑' γ : SL(2, 𝓞 K), (boxT t α β).indicator 1 (slAct (Equiv.mulRight g⁻¹ γ) (slAct g p)) := by
        refine tsum_congr fun γ => ?_
        rw [Equiv.coe_mulRight, ← slAct_mul _ _ hp, inv_mul_cancel_right]
    _ = ∑' γ : SL(2, 𝓞 K), (boxT t α β).indicator 1 (slAct γ (slAct g p)) :=
        (Equiv.mulRight g⁻¹).tsum_eq (fun γ => (boxT t α β).indicator 1 (slAct γ (slAct g p)))
    _ ≤ cBox α := tsum_boxT_le_of_siegel t hα β hg

/-- The box `{(z, v) : |z| ≤ Z, α ≤ v ≤ β}`. -/
def boxZ (Z α β : ℝ) : Set (ℂ × ℝ) := {p | ‖p.1‖ ≤ Z ∧ α ≤ p.2 ∧ p.2 ≤ β}

theorem measurableSet_boxZ (Z α β : ℝ) : MeasurableSet (boxZ Z α β) :=
  (measurableSet_le (measurable_fst.norm) measurable_const).inter
    ((measurableSet_le measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd measurable_const))

/-- The number of `t` with `|σ(t)| ≤ Z + 2`, enough to cover `{|z| ≤ Z}` by the translates `P + σ(t)`. -/
def cTr (Z : ℝ) : ℝ≥0∞ := ∑' t : 𝓞 K, {t : 𝓞 K | Complex.normSq (σO t) ≤ (Z + 2) ^ 2}.indicator 1 t

theorem cTr_ne_top (Z : ℝ) : cTr Z ≠ ⊤ := by
  have hfin := finite_normSq_le ((Z + 2) ^ 2)
  unfold cTr
  rw [tsum_eq_sum (s := hfin.toFinset) fun t ht => ?_]
  · refine ENNReal.sum_ne_top.2 fun t _ => ?_
    by_cases h : t ∈ {t : 𝓞 K | Complex.normSq (σO t) ≤ (Z + 2) ^ 2}
    · rw [Set.indicator_of_mem h]; simp
    · rw [Set.indicator_of_notMem h]; simp
  · rw [Set.Finite.mem_toFinset] at ht
    exact Set.indicator_of_notMem ht _

/-- **Uniformly finitely many translates of a point lie in a box `boxZ Z α β`**, `α > 0`. -/
theorem tsum_boxZ_le (Z : ℝ) {α : ℝ} (hα : 0 < α) (β : ℝ) {p : ℂ × ℝ} (hp : p ∈ UHS) :
    ∑' γ : SL(2, 𝓞 K), (boxZ Z α β).indicator 1 (slAct γ p) ≤ cTr Z * cBox α := by
  set T : Set (𝓞 K) := {t : 𝓞 K | Complex.normSq (σO t) ≤ (Z + 2) ^ 2} with hT
  have hcov : ∀ q : ℂ × ℝ, (boxZ Z α β).indicator (1 : ℂ × ℝ → ℝ≥0∞) q ≤
      ∑' t : 𝓞 K, T.indicator (1 : 𝓞 K → ℝ≥0∞) t * (boxT t α β).indicator (1 : ℂ × ℝ → ℝ≥0∞) q := by
    intro q
    by_cases hq : q ∈ boxZ Z α β
    · rw [Set.indicator_of_mem hq, Pi.one_apply]
      obtain ⟨t', ht'⟩ := exists_transl_mem_fundP q.1
      have hmem : q ∈ boxT (-t') α β := ⟨by rwa [map_neg, sub_neg_eq_add], hq.2.1, hq.2.2⟩
      have hTm : -t' ∈ T := by
        show Complex.normSq (σO (-t')) ≤ (Z + 2) ^ 2
        rw [Complex.normSq_eq_norm_sq, map_neg, norm_neg]
        have h2 := norm_le_two_of_mem_fundP ht'
        have h3 : ‖σO t'‖ ≤ Z + 2 := by
          calc ‖σO t'‖ = ‖(q.1 + σO t') - q.1‖ := by ring_nf
            _ ≤ ‖q.1 + σO t'‖ + ‖q.1‖ := norm_sub_le _ _
            _ ≤ Z + 2 := by linarith [hq.1]
        exact pow_le_pow_left₀ (norm_nonneg _) h3 2
      calc (1 : ℝ≥0∞) = T.indicator 1 (-t') * (boxT (-t') α β).indicator 1 q := by
            rw [Set.indicator_of_mem hTm, Set.indicator_of_mem hmem]
            simp only [Pi.one_apply, one_mul]
        _ ≤ ∑' t : 𝓞 K, T.indicator 1 t * (boxT t α β).indicator 1 q :=
            ENNReal.le_tsum (f := fun t => T.indicator 1 t * (boxT t α β).indicator 1 q) (-t')
    · rw [Set.indicator_of_notMem hq]
      exact zero_le
  calc ∑' γ : SL(2, 𝓞 K), (boxZ Z α β).indicator 1 (slAct γ p)
      ≤ ∑' γ : SL(2, 𝓞 K), ∑' t : 𝓞 K, T.indicator 1 t * (boxT t α β).indicator 1 (slAct γ p) :=
        ENNReal.tsum_le_tsum fun γ => hcov _
    _ = ∑' t : 𝓞 K, T.indicator 1 t * ∑' γ : SL(2, 𝓞 K), (boxT t α β).indicator 1 (slAct γ p) := by
        rw [ENNReal.tsum_comm]
        refine tsum_congr fun t => ?_
        rw [ENNReal.tsum_mul_left]
    _ ≤ ∑' t : 𝓞 K, T.indicator 1 t * cBox α :=
        ENNReal.tsum_le_tsum fun t => by gcongr; exact tsum_boxT_le t hα β hp
    _ = cTr Z * cBox α := by rw [ENNReal.tsum_mul_right]; rfl

/-! ### Local integrability of automorphic functions -/

instance isFiniteMeasure_muR_rhoG : IsFiniteMeasure (muR rhoG) := by
  refine ⟨?_⟩
  rw [muR, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have h := lintegral_puLe_top_mul_lt_top Gam3 (F := fun _ => 1) measurable_const
    (fun _ => ⟨1, ENNReal.one_ne_top, fun _ _ => le_rfl⟩)
  simpa [rhoG] using h

/-- **An automorphic function in `L¹(ν)` is integrable on every box** `{|z| ≤ Z, α ≤ v ≤ β}` with `α > 0`:
unfolding with the partition of unity (round 386's `lintegral_unfold`) and `tsum_boxZ_le`. -/
theorem lintegral_boxZ_lt_top {u : ℂ × ℝ → ℂ} (hum : Measurable u)
    (hinv : ∀ γ ∈ Gam3, ∀ p ∈ UHS, ‖u (slAct γ p)‖ₑ = ‖u p‖ₑ)
    (hu : ∫⁻ p, ‖u p‖ₑ ∂(muR rhoG) < ⊤) (Z : ℝ) {α : ℝ} (hα : 0 < α) (β : ℝ) :
    ∫⁻ p in boxZ Z α β, ‖u p‖ₑ ∂uhsMeasure < ⊤ := by
  set B := boxZ Z α β with hBdef
  have hB : MeasurableSet B := measurableSet_boxZ Z α β
  have hg : Measurable fun q : ℂ × ℝ => ‖u q‖ₑ := hum.enorm
  rw [← lintegral_indicator hB]
  rw [← lintegral_unfold isPU_rhoG (Φ := fun γ p => B.indicator (fun q => ‖u q‖ₑ) (slAct γ p))
    (Ψ := B.indicator (fun q => ‖u q‖ₑ)) (fun γ => (hg.indicator hB).comp (measurable_slAct _))
    (hg.indicator hB) (fun γ q hq => by
      show B.indicator (fun q => ‖u q‖ₑ) (slAct (γ : SL(2, 𝓞 K)) (slAct ((γ⁻¹ : Gam3) : SL(2, 𝓞 K)) q)) =
        B.indicator (fun q => ‖u q‖ₑ) q
      rw [← slAct_mul _ _ hq, Subgroup.coe_inv, mul_inv_cancel, slAct_one])]
  have hpt : ∀ p ∈ UHS, rhoG p * ∑' γ : Gam3, B.indicator (fun q => ‖u q‖ₑ) (slAct γ p) ≤
      cTr Z * cBox α * (rhoG p * ‖u p‖ₑ) := by
    intro p hp
    have e : ∑' γ : Gam3, B.indicator (fun q => ‖u q‖ₑ) (slAct γ p) =
        (∑' γ : Gam3, B.indicator (1 : ℂ × ℝ → ℝ≥0∞) (slAct γ p)) * ‖u p‖ₑ := by
      rw [← ENNReal.tsum_mul_right]
      refine tsum_congr fun γ => ?_
      by_cases h : slAct γ p ∈ B
      · rw [indicator_of_mem h, indicator_of_mem h, Pi.one_apply, one_mul, hinv γ γ.2 p hp]
      · rw [indicator_of_notMem h, indicator_of_notMem h, zero_mul]
    have hle : ∑' γ : Gam3, B.indicator (1 : ℂ × ℝ → ℝ≥0∞) (slAct γ p) ≤ cTr Z * cBox α :=
      (ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective
        (fun γ => B.indicator (1 : ℂ × ℝ → ℝ≥0∞) (slAct γ p))).trans (tsum_boxZ_le Z hα β hp)
    rw [e]
    calc rhoG p * ((∑' γ : Gam3, B.indicator (1 : ℂ × ℝ → ℝ≥0∞) (slAct γ p)) * ‖u p‖ₑ)
        ≤ rhoG p * (cTr Z * cBox α * ‖u p‖ₑ) := by gcongr
      _ = cTr Z * cBox α * (rhoG p * ‖u p‖ₑ) := by ring
  calc ∫⁻ p, rhoG p * ∑' γ : Gam3, B.indicator (fun q => ‖u q‖ₑ) (slAct γ p) ∂uhsMeasure
      ≤ ∫⁻ p, cTr Z * cBox α * (rhoG p * ‖u p‖ₑ) ∂uhsMeasure := by
        refine lintegral_mono_ae ?_
        filter_upwards [ae_UHS] with p hp
        exact hpt p hp
    _ = cTr Z * cBox α * ∫⁻ p, ‖u p‖ₑ ∂(muR rhoG) := by
        rw [lintegral_const_mul _ (show Measurable fun p => rhoG p * ‖u p‖ₑ from isPU_rhoG.1.mul hg), muR,
          lintegral_withDensity_eq_lintegral_mul _ isPU_rhoG.1 hg]
        rfl
    _ < ⊤ := ENNReal.mul_lt_top (ENNReal.mul_lt_top (cTr_ne_top Z).lt_top (cBox_ne_top α).lt_top) hu

/-! ### θ's representative -/

theorem measurable_thetaF (r Y : ℝ) (hY : 0 < Y) : Measurable (thetaF r Y hY) := by
  have h : StronglyMeasurable (fun x : (ℂ × ℝ) × (ℂ × ℝ) =>
      bker Gam3 (fun g => kub ↑g) (2 * Real.cosh r - 2) x.1 x.2 * (thetaL r Y hY : ℂ × ℝ → ℂ) x.2) :=
    ((measurable_bker _ _ _).mul
      ((Lp.stronglyMeasurable (thetaL r Y hY)).measurable.comp measurable_snd)).stronglyMeasurable
  have hk : Measurable (kfun Gam3 (fun g => kub ↑g) (2 * Real.cosh r - 2) rhoG (thetaL r Y hY)) :=
    (h.integral_prod_right' (ν := muR rhoG)).measurable
  unfold thetaF
  exact hk.const_smul _

theorem memLp_thetaF {r : ℝ} (hr : 0 < r) {Y : ℝ} (hY : 0 < Y) : MemLp (thetaF r Y hY) 2 (muR rhoG) :=
  (Lp.memLp (thetaL r Y hY)).ae_eq (thetaL_ae_eq_thetaF hr hY)

theorem enorm_thetaF_slAct (r Y : ℝ) (hY : 0 < Y) :
    ∀ γ ∈ Gam3, ∀ p ∈ UHS, ‖thetaF r Y hY (slAct γ p)‖ₑ = ‖thetaF r Y hY p‖ₑ := by
  intro γ hγ p hp
  rw [isAut_thetaF r Y hY γ hγ p hp, enorm_mul]
  have h1 : ‖kub (↑γ : Matrix (Fin 2) (Fin 2) (𝓞 K))‖ₑ = 1 := by
    rw [← ofReal_norm, isUChar_kub.norm_eq γ hγ, ENNReal.ofReal_one]
  rw [h1, one_mul]

/-- **θ's representative is integrable on every box** `{|z| ≤ Z, α ≤ v ≤ β}`, `α > 0`. -/
theorem lintegral_boxZ_thetaF_lt_top {r : ℝ} (hr : 0 < r) {Y : ℝ} (hY : 0 < Y) (Z : ℝ) {α : ℝ}
    (hα : 0 < α) (β : ℝ) : ∫⁻ p in boxZ Z α β, ‖thetaF r Y hY p‖ₑ ∂uhsMeasure < ⊤ :=
  lintegral_boxZ_lt_top (measurable_thetaF r Y hY) (enorm_thetaF_slAct r Y hY)
    ((memLp_thetaF hr hY).integrable one_le_two).2 Z hα β

/-! ### Unfolding `P_m(ψ)` against θ -/

/-- `∫_T f dz dv ≤ β³·∫_T f dz dv/v³` for `T` inside `{α ≤ v ≤ β}`, `α > 0`. -/
theorem setLIntegral_volume_le {f : ℂ × ℝ → ℝ≥0∞} (hf : Measurable f) {T : Set (ℂ × ℝ)}
    (hT : MeasurableSet T) {α β : ℝ} (hα : 0 < α) (hTs : ∀ p ∈ T, α ≤ p.2 ∧ p.2 ≤ β) :
    ∫⁻ p in T, f p ∂volume ≤ ENNReal.ofReal (β ^ 3) * ∫⁻ p in T, f p ∂uhsMeasure := by
  have hTU : T ⊆ UHS := fun p hp => show (0 : ℝ) < p.2 from lt_of_lt_of_le hα (hTs p hp).1
  rw [uhsMeasure, setLIntegral_withDensity_eq_setLIntegral_mul _ measurable_uhsW hf hT,
    Measure.restrict_restrict hT, inter_eq_left.2 hTU, ← lintegral_const_mul _ (measurable_uhsW.mul hf)]
  refine setLIntegral_mono ((measurable_const.mul (measurable_uhsW.mul hf))) fun p hp => ?_
  have hv : 0 < p.2 := lt_of_lt_of_le hα (hTs p hp).1
  have hβ : 0 < β := lt_of_lt_of_le hv (hTs p hp).2
  have h1 : 1 ≤ β ^ 3 * p.2 ^ (-3 : ℤ) := by
    rw [zpow_neg, show ((3 : ℤ)) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast, ← div_eq_mul_inv,
      le_div_iff₀ (by positivity), one_mul]
    exact pow_le_pow_left₀ hv.le (hTs p hp).2 3
  calc f p = 1 * f p := (one_mul _).symm
    _ ≤ ENNReal.ofReal (β ^ 3 * p.2 ^ (-3 : ℤ)) * f p := by
        gcongr
        rw [← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal h1
    _ = ENNReal.ofReal (β ^ 3) * (uhsW * f) p := by
        rw [ENNReal.ofReal_mul (by positivity), Pi.mul_apply, uhsW, mul_assoc]

/-- **Fubini on `3P × (0, ∞)`** for `F` integrable on `3P × [α, β]` (round 430's `integral_fundP3_conj_mul`
asks for a bound). -/
theorem integral_fundP3_conj_mul_of_int {ψ : ℝ → ℂ} (hψ : Measurable ψ) {M α β : ℝ}
    (hM : ∀ v, ‖ψ v‖ ≤ M) (hψ0 : ∀ v, v ∉ Icc α β → ψ v = 0) (hα : 0 < α) {F : ℂ × ℝ → ℂ}
    (hF : Measurable F) (hFi : IntegrableOn F (fundP3 ×ˢ Icc α β)) :
    ∫ p in Prod.fst ⁻¹' fundP3, conj (ψ p.2) * F p ∂uhsMeasure =
      ∫ v in Ioi 0, ((v ^ (-3 : ℤ) : ℝ) : ℂ) * conj (ψ v) * ∫ z in fundP3, F (z, v) := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  set T : Set (ℂ × ℝ) := fundP3 ×ˢ Icc α β with hTdef
  set H : ℂ × ℝ → ℂ := fun q => ((q.2 ^ (-3 : ℤ) : ℝ) : ℂ) * (conj (ψ q.2) * F q) with hHdef
  have hT : MeasurableSet T := measurableSet_fundP3.prod measurableSet_Icc
  have hHm : Measurable H := by
    have : Measurable fun q : ℂ × ℝ => ((q.2 ^ (-3 : ℤ) : ℝ) : ℂ) := by fun_prop
    exact this.mul ((Complex.continuous_conj.measurable.comp (hψ.comp measurable_snd)).mul hF)
  have hstep1 : ∫ p in Prod.fst ⁻¹' fundP3, conj (ψ p.2) * F p ∂uhsMeasure = ∫ q, T.indicator H q := by
    rw [← integral_indicator (measurableSet_fundP3.preimage measurable_fst), uhsMeasure,
      integral_withDensity_eq_integral_toReal_smul measurable_uhsW
        (Eventually.of_forall fun q => ENNReal.ofReal_lt_top),
      ← integral_indicator measurableSet_UHS]
    refine integral_congr_ae (Eventually.of_forall fun q => ?_)
    by_cases hq : q ∈ T
    · have hv : 0 < q.2 := lt_of_lt_of_le hα hq.2.1
      have hq' : q ∈ UHS := hv
      rw [indicator_of_mem hq', indicator_of_mem (show q ∈ Prod.fst ⁻¹' fundP3 from hq.1),
        indicator_of_mem hq, uhsW, ENNReal.toReal_ofReal (by positivity), Complex.real_smul]
    · rw [indicator_of_notMem hq]
      by_cases hq' : q ∈ UHS
      · rw [indicator_of_mem hq']
        by_cases h3 : q.1 ∈ fundP3
        · have h4 : q.2 ∉ Icc α β := fun h => hq ⟨h3, h⟩
          rw [indicator_of_mem (show q ∈ Prod.fst ⁻¹' fundP3 from h3), hψ0 _ h4, map_zero, zero_mul,
            smul_zero]
        · rw [indicator_of_notMem (show q ∉ Prod.fst ⁻¹' fundP3 from h3), smul_zero]
      · rw [indicator_of_notMem hq']
  have hint : Integrable (T.indicator H) (volume : Measure (ℂ × ℝ)) := by
    rw [integrable_indicator_iff hT]
    refine (hFi.norm.const_mul (α ^ (-3 : ℤ) * M)).mono' hHm.aestronglyMeasurable ?_
    rw [ae_restrict_iff' hT]
    refine Eventually.of_forall fun q hq => ?_
    have hv : 0 < q.2 := lt_of_lt_of_le hα hq.2.1
    simp only [hHdef]
    rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity)]
    calc q.2 ^ (-3 : ℤ) * (‖ψ q.2‖ * ‖F q‖) ≤ α ^ (-3 : ℤ) * (M * ‖F q‖) :=
          mul_le_mul (zpow_neg_three_le hα hq.2.1)
            (mul_le_mul_of_nonneg_right (hM _) (norm_nonneg _)) (by positivity) (by positivity)
      _ = α ^ (-3 : ℤ) * M * ‖F q‖ := by ring
  have hslice : ∀ v : ℝ, ∫ z, T.indicator H (z, v) = (Ioi (0 : ℝ)).indicator
      (fun v => ((v ^ (-3 : ℤ) : ℝ) : ℂ) * conj (ψ v) * ∫ z in fundP3, F (z, v)) v := by
    intro v
    by_cases hv : v ∈ Icc α β
    · have hv0 : 0 < v := lt_of_lt_of_le hα hv.1
      rw [indicator_of_mem (show v ∈ Ioi (0 : ℝ) from hv0)]
      have e : (fun z => T.indicator H (z, v)) = fundP3.indicator (fun z => H (z, v)) := by
        funext z
        by_cases hz : z ∈ fundP3
        · rw [indicator_of_mem (show (z, v) ∈ T from ⟨hz, hv⟩), indicator_of_mem hz]
        · rw [indicator_of_notMem (show (z, v) ∉ T from fun h => hz h.1), indicator_of_notMem hz]
      rw [e, integral_indicator measurableSet_fundP3]
      simp only [hHdef]
      rw [integral_const_mul, integral_const_mul]
      ring
    · have e : (fun z => T.indicator H (z, v)) = fun _ => 0 := by
        funext z
        rw [indicator_of_notMem (show (z, v) ∉ T from fun h => hv h.2)]
      rw [e, integral_zero]
      by_cases hv0 : v ∈ Ioi (0 : ℝ)
      · rw [indicator_of_mem hv0, hψ0 v hv, map_zero, mul_zero, zero_mul]
      · rw [indicator_of_notMem hv0]
  rw [hstep1, Measure.volume_eq_prod,
    integral_prod_symm _ (by rw [← Measure.volume_eq_prod]; exact hint)]
  simp_rw [hslice]
  rw [integral_indicator measurableSet_Ioi]

/-- **The pairing of θ with `P_m(ψ)`, unfolded**: for `ψ` measurable and bounded, vanishing outside `[α, β]`
with `α > 0`, `⟨P_m(ψ), θ⟩ = ∫_0^∞ v^{−3}·conj ψ(v)·∫_{3P} ĕ(−mz/9)θ̃(z, v) dz dv`, with `θ̃` round 425's
representative of θ. -/
theorem inner_pmSer_thetaL_unfold (x : 𝓞 K) {r : ℝ} (hr : 0 < r) {Y : ℝ} (hY : 0 < Y) {ψ : ℝ → ℂ}
    (hψ : Measurable ψ) (hψ2 : MemLp (pmSer (δ3 * x) ψ) 2 (muR rhoG)) {M α β : ℝ}
    (hM : ∀ v, ‖ψ v‖ ≤ M) (hψ0 : ∀ v, v ∉ Icc α β → ψ v = 0) (hα : 0 < α) :
    inner ℂ (hψ2.toLp (pmSer (δ3 * x) ψ)) (thetaL r Y hY) =
      ∫ v in Ioi 0, ((v ^ (-3 : ℤ) : ℝ) : ℂ) * conj (ψ v) *
        ∫ z in fundP3, ebr (-(σO (δ3 * x) / 9 * z)) * thetaF r Y hY (z, v) := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  set m := δ3 * x with hm
  set θt := thetaF r Y hY with hθt
  have hθ : thetaL r Y hY = (memLp_thetaF hr hY).toLp θt :=
    Lp.ext ((thetaL_ae_eq_thetaF hr hY).trans (memLp_thetaF hr hY).coeFn_toLp.symm)
  have hbox := lintegral_boxZ_thetaF_lt_top hr hY 6 hα β
  have hT : MeasurableSet (fundP3 ×ˢ Icc α β) := measurableSet_fundP3.prod measurableSet_Icc
  have hTb : ∀ p ∈ fundP3 ×ˢ Icc α β, p ∈ boxZ 6 α β := fun p hp =>
    ⟨norm_le_six_of_mem_fundP3 hp.1, hp.2.1, hp.2.2⟩
  -- the absolute convergence of the unfolding
  have hfin : ∫⁻ p, rhoT3 p * ‖conj (ψ p.2 * ebr (σO m * p.1 / 9)) * θt p‖ₑ ∂uhsMeasure ≠ ⊤ := by
    refine ne_top_of_le_ne_top (b := ∫⁻ p in boxZ 6 α β, ENNReal.ofReal M * ‖θt p‖ₑ ∂uhsMeasure) ?_ ?_
    · rw [lintegral_const_mul _ (measurable_thetaF r Y hY).enorm]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hbox.ne
    · rw [← lintegral_indicator (measurableSet_boxZ 6 α β)]
      refine lintegral_mono fun p => ?_
      by_cases hp : p ∈ fundP3 ×ˢ Icc α β
      · rw [indicator_of_mem (hTb p hp)]
        calc rhoT3 p * ‖conj (ψ p.2 * ebr (σO m * p.1 / 9)) * θt p‖ₑ
            ≤ 1 * ‖conj (ψ p.2 * ebr (σO m * p.1 / 9)) * θt p‖ₑ := by
              gcongr
              exact rhoT3_le_one p
          _ ≤ ENNReal.ofReal M * ‖θt p‖ₑ := by
              rw [one_mul, enorm_mul, ← ofReal_norm (conj _), Complex.norm_conj, norm_mul, norm_ebr,
                mul_one]
              gcongr
              exact hM _
      · by_cases h3 : p.1 ∈ fundP3
        · have h4 : p.2 ∉ Icc α β := fun h => hp ⟨h3, h⟩
          rw [hψ0 _ h4, zero_mul, map_zero, zero_mul, enorm_zero, mul_zero]
          exact zero_le
        · have h0 : rhoT3 p = 0 := by
            unfold rhoT3
            rw [indicator_of_notMem h3]
          rw [h0, zero_mul]
          exact zero_le
  have hme : Measurable fun p : ℂ × ℝ => conj (ebr (σO m * p.1 / 9)) :=
    Complex.continuous_conj.measurable.comp
      (measurable_ebr.comp ((measurable_const.mul measurable_fst).div_const 9))
  set Fθ : ℂ × ℝ → ℂ := fun p => conj (ebr (σO m * p.1 / 9)) * θt p with hFθ
  have hFm : Measurable Fθ := hme.mul (measurable_thetaF r Y hY)
  have hFi : IntegrableOn Fθ (fundP3 ×ˢ Icc α β) := by
    refine ⟨hFm.aestronglyMeasurable, ?_⟩
    show ∫⁻ p in fundP3 ×ˢ Icc α β, ‖Fθ p‖ₑ < ⊤
    have e : ∀ p, ‖Fθ p‖ₑ = ‖θt p‖ₑ := fun p => by
      simp only [hFθ]
      rw [enorm_mul, ← ofReal_norm (conj _), Complex.norm_conj, norm_ebr, ENNReal.ofReal_one, one_mul]
    simp_rw [e]
    refine (setLIntegral_volume_le (measurable_thetaF r Y hY).enorm hT hα
      (fun p hp => ⟨hp.2.1, hp.2.2⟩)).trans_lt ?_
    refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
    exact (lintegral_mono_set (fun p hp => hTb p hp)).trans_lt hbox
  rw [hθ, inner_toLp_pmSer hψ hψ2 (isAut_thetaF r Y hY) (measurable_thetaF r Y hY) (memLp_thetaF hr hY)
    hfin]
  have e1 : ∫ p in Prod.fst ⁻¹' fundP3, conj (ψ p.2 * ebr (σO m * p.1 / 9)) * θt p ∂uhsMeasure =
      ∫ p in Prod.fst ⁻¹' fundP3, conj (ψ p.2) * Fθ p ∂uhsMeasure := by
    refine setIntegral_congr_fun (measurableSet_fundP3.preimage measurable_fst) fun p _ => ?_
    simp only [hFθ]
    rw [map_mul]
    ring
  rw [e1, integral_fundP3_conj_mul_of_int hψ hM hψ0 hα hFm hFi]
  refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
  simp only [hFθ]
  congr 1
  refine setIntegral_congr_fun measurableSet_fundP3 fun z _ => ?_
  rw [conj_ebr, hm]
  congr 2
  ring

/-! ### The Fourier coefficients of θ -/

/-- Fubini's slice: for `F` integrable on `3P × [α, β]`, `v ↦ ∫_{3P} F(z, v) dz` is integrable on `[α, β]`. -/
theorem integrableOn_slice {F : ℂ × ℝ → ℂ} {α β : ℝ} (hFi : IntegrableOn F (fundP3 ×ˢ Icc α β)) :
    IntegrableOn (fun v => ∫ z in fundP3, F (z, v)) (Icc α β) := by
  have h : Integrable F ((volume.restrict fundP3).prod (volume.restrict (Icc α β))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact hFi
  exact h.integral_prod_right

/-- `ĕ(−mz/9)·θ̃(z, v)` is integrable on `3P × [α, β]` for `α > 0`. -/
theorem integrableOn_ebr_thetaF (x : 𝓞 K) {r : ℝ} (hr : 0 < r) {Y : ℝ} (hY : 0 < Y) {α : ℝ} (hα : 0 < α)
    (β : ℝ) : IntegrableOn (fun p : ℂ × ℝ => ebr (-(σO (δ3 * x) / 9 * p.1)) * thetaF r Y hY p)
      (fundP3 ×ˢ Icc α β) := by
  have hT : MeasurableSet (fundP3 ×ˢ Icc α β) := measurableSet_fundP3.prod measurableSet_Icc
  have hm : Measurable fun p : ℂ × ℝ => ebr (-(σO (δ3 * x) / 9 * p.1)) * thetaF r Y hY p :=
    (measurable_ebr.comp (measurable_const.mul measurable_fst).neg).mul (measurable_thetaF r Y hY)
  refine ⟨hm.aestronglyMeasurable, ?_⟩
  show ∫⁻ p in fundP3 ×ˢ Icc α β, ‖ebr (-(σO (δ3 * x) / 9 * p.1)) * thetaF r Y hY p‖ₑ < ⊤
  have e : ∀ p : ℂ × ℝ, ‖ebr (-(σO (δ3 * x) / 9 * p.1)) * thetaF r Y hY p‖ₑ = ‖thetaF r Y hY p‖ₑ :=
    fun p => by rw [enorm_mul, ← ofReal_norm (ebr _), norm_ebr, ENNReal.ofReal_one, one_mul]
  simp_rw [e]
  refine (setLIntegral_volume_le (measurable_thetaF r Y hY).enorm hT hα
    (fun p hp => ⟨hp.2.1, hp.2.2⟩)).trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_)
  exact (lintegral_mono_set (fun p hp => (⟨norm_le_six_of_mem_fundP3 hp.1, hp.2.1, hp.2.2⟩ :
    p ∈ boxZ 6 α β))).trans_lt (lintegral_boxZ_thetaF_lt_top hr hY 6 hα β)

/-- `(0, ∞) = ⋃_n [1/(n + 1), n + 1]`. -/
theorem Ioi_zero_eq_iUnion_Icc : Ioi (0 : ℝ) = ⋃ n : ℕ, Icc (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1) := by
  ext v
  simp only [mem_Ioi, mem_iUnion, mem_Icc]
  constructor
  · intro hv
    obtain ⟨n, hn⟩ := exists_nat_gt (max v (1 / v))
    have h1 : v < (n : ℝ) + 1 := by linarith [le_max_left v (1 / v)]
    have h2 : 1 / v < (n : ℝ) + 1 := by linarith [le_max_right v (1 / v)]
    refine ⟨n, ?_, h1.le⟩
    rw [div_le_iff₀ (by positivity)]
    rw [div_lt_iff₀ hv] at h2
    linarith
  · rintro ⟨n, h1, -⟩
    exact lt_of_lt_of_le (by positivity) h1

/-- **The Fourier coefficients of θ**: for `m = δ₃x ≠ 0`, `r > 0` and `Y > 0`, for almost every `v > 0`,
`∫_{3P} ĕ(−mz/9)θ̃(z, v) dz = ρ(m)·v·K_{1/3}(4π|m|v/9)`, with `θ̃` round 425's representative of θ and
`ρ(m)` round 431's `rhoM`. -/
theorem coef_thetaF_ae {x : 𝓞 K} (hx : x ≠ 0) {r : ℝ} (hr : 0 < r) {Y : ℝ} (hY : 0 < Y) :
    ∀ᵐ v ∂(volume.restrict (Ioi (0 : ℝ))),
      ∫ z in fundP3, ebr (-(σO (δ3 * x) / 9 * z)) * thetaF r Y hY (z, v) =
        rhoM x r Y hY * ((v : ℂ) * besselK (1 / 3) (4 * Real.pi * ‖σO (δ3 * x) / 9‖ * v)) := by
  have hξ : σO (δ3 * x) / 9 ≠ 0 :=
    div_ne_zero (σO_ne_zero (mul_ne_zero δ3_ne_zero hx)) (by norm_num)
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = 4 * Real.pi * ‖σO (δ3 * x) / 9‖ := ⟨_, rfl⟩
  have hApos : 0 < A := by
    have := norm_pos_iff.2 hξ
    rw [hA]
    positivity
  rw [← hA]
  set a : ℝ → ℂ := fun v => ∫ z in fundP3, ebr (-(σO (δ3 * x) / 9 * z)) * thetaF r Y hY (z, v) with ha
  set ρ := rhoM x r Y hY with hρ
  set g : ℝ → ℂ := fun v => ((v ^ (-3 : ℤ) : ℝ) : ℂ) * a v -
    ρ * (((v ^ (-2 : ℤ) : ℝ) : ℂ) * besselK (4 / 3 - 1) (A * v)) with hg
  have key : ∀ n : ℕ, ∀ᵐ v ∂(volume.restrict (Icc (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1))), g v = 0 := by
    intro n
    obtain ⟨α, hαdef⟩ : ∃ α : ℝ, α = 1 / ((n : ℝ) + 1) := ⟨_, rfl⟩
    obtain ⟨β, hβdef⟩ : ∃ β : ℝ, β = (n : ℝ) + 1 := ⟨_, rfl⟩
    rw [← hαdef, ← hβdef]
    have h1n : (1 : ℝ) ≤ (n : ℝ) + 1 := by
      have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
      linarith
    have hα : 0 < α := by rw [hαdef]; positivity
    have hαβ : α ≤ β := by
      rw [hαdef, hβdef]
      exact ((div_le_one (by positivity)).2 h1n).trans h1n
    have hsub : Icc α β ⊆ Ioi 0 := fun v hv => lt_of_lt_of_le hα hv.1
    -- integrability of the two parts on `[α, β]`
    have hai : IntegrableOn a (Icc α β) :=
      integrableOn_slice (integrableOn_ebr_thetaF x hr hY hα β)
    have h3i : IntegrableOn (fun v => ((v ^ (-3 : ℤ) : ℝ) : ℂ) * a v) (Icc α β) := by
      refine (hai.norm.const_mul (α ^ (-3 : ℤ))).mono' ?_ ?_
      · have hc : Measurable fun v : ℝ => ((v ^ (-3 : ℤ) : ℝ) : ℂ) := by fun_prop
        exact hc.aestronglyMeasurable.mul hai.aestronglyMeasurable
      · rw [ae_restrict_iff' measurableSet_Icc]
        refine Eventually.of_forall fun v hv => ?_
        have hv0 : 0 < v := lt_of_lt_of_le hα hv.1
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
        exact mul_le_mul_of_nonneg_right (zpow_neg_three_le hα hv.1) (norm_nonneg _)
    have hKi : IntegrableOn (fun v : ℝ => ((v ^ (-2 : ℤ) : ℝ) : ℂ) * besselK (4 / 3 - 1) (A * v))
        (Icc α β) :=
      ((continuousOn_zpow_besselK (4 / 3 - 1) hApos).mono hsub).integrableOn_compact isCompact_Icc
    have hgi : IntegrableOn g (Icc α β) := h3i.sub (hKi.const_mul ρ)
    refine hgi.ae_eq_zero_of_forall_setIntegral_eq_zero fun s hs _ => ?_
    rw [Measure.restrict_restrict hs]
    -- the profile `1_{s ∩ [α, β]}`
    obtain ⟨S, hS⟩ : ∃ S : Set ℝ, S = s ∩ Icc α β := ⟨_, rfl⟩
    rw [← hS]
    have hSm : MeasurableSet S := by rw [hS]; exact hs.inter measurableSet_Icc
    have hSI : S ⊆ Icc α β := by rw [hS]; exact inter_subset_right
    have hSsub : S ⊆ Ioi 0 := hSI.trans hsub
    obtain ⟨ψ, hψdef⟩ : ∃ ψ : ℝ → ℂ, ψ = S.indicator fun _ => 1 := ⟨_, rfl⟩
    have hψm : Measurable ψ := by rw [hψdef]; exact measurable_const.indicator hSm
    have hψM : ∀ v, ‖ψ v‖ ≤ 1 := fun v => by
      by_cases h : v ∈ S
      · rw [hψdef, indicator_of_mem h, norm_one]
      · rw [hψdef, indicator_of_notMem h, norm_zero]
        norm_num
    have hψ0 : ∀ v, v ∉ Icc α β → ψ v = 0 := fun v hv => by
      rw [hψdef, indicator_of_notMem fun h => hv (hSI h)]
    have hψ2 := memLp_pmSer_Icc (δ3 * x) hψm hψM hψ0 hα
    have h1 := inner_pmSer_thetaL_unfold x hr hY hψm hψ2 hψM hψ0 hα
    have h2 := inner_pmSer_thetaL hx hr hY hψm hψ2 hψM hψ0 hα hαβ
    rw [← hA] at h2
    rw [h1] at h2
    unfold jPsi at h2
    have e1 : ∫ v in Ioi 0, ((v ^ (-3 : ℤ) : ℝ) : ℂ) * conj (ψ v) * a v =
        ∫ v in S, ((v ^ (-3 : ℤ) : ℝ) : ℂ) * a v := by
      calc ∫ v in Ioi 0, ((v ^ (-3 : ℤ) : ℝ) : ℂ) * conj (ψ v) * a v
          = ∫ v in Ioi 0, S.indicator (fun v => ((v ^ (-3 : ℤ) : ℝ) : ℂ) * a v) v := by
            refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
            by_cases h : v ∈ S
            · rw [hψdef, indicator_of_mem h, indicator_of_mem h, map_one, mul_one]
            · rw [hψdef, indicator_of_notMem h, indicator_of_notMem h, map_zero, mul_zero, zero_mul]
        _ = ∫ v in Ioi 0 ∩ S, ((v ^ (-3 : ℤ) : ℝ) : ℂ) * a v := setIntegral_indicator hSm
        _ = ∫ v in S, ((v ^ (-3 : ℤ) : ℝ) : ℂ) * a v := by rw [inter_eq_right.2 hSsub]
    have e2 : ∫ v in Ioi 0, conj (ψ v) * (((v ^ (-2 : ℤ) : ℝ) : ℂ) * besselK (4 / 3 - 1) (A * v)) =
        ∫ v in S, ((v ^ (-2 : ℤ) : ℝ) : ℂ) * besselK (4 / 3 - 1) (A * v) := by
      calc ∫ v in Ioi 0, conj (ψ v) * (((v ^ (-2 : ℤ) : ℝ) : ℂ) * besselK (4 / 3 - 1) (A * v))
          = ∫ v in Ioi 0, S.indicator
              (fun v => ((v ^ (-2 : ℤ) : ℝ) : ℂ) * besselK (4 / 3 - 1) (A * v)) v := by
            refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
            by_cases h : v ∈ S
            · rw [hψdef, indicator_of_mem h, indicator_of_mem h, map_one, one_mul]
            · rw [hψdef, indicator_of_notMem h, indicator_of_notMem h, map_zero, zero_mul]
        _ = ∫ v in Ioi 0 ∩ S, ((v ^ (-2 : ℤ) : ℝ) : ℂ) * besselK (4 / 3 - 1) (A * v) :=
            setIntegral_indicator hSm
        _ = ∫ v in S, ((v ^ (-2 : ℤ) : ℝ) : ℂ) * besselK (4 / 3 - 1) (A * v) := by
            rw [inter_eq_right.2 hSsub]
    rw [e1, e2] at h2
    have hS3 : IntegrableOn (fun v => ((v ^ (-3 : ℤ) : ℝ) : ℂ) * a v) S := h3i.mono_set hSI
    have hSK : IntegrableOn (fun v : ℝ => ((v ^ (-2 : ℤ) : ℝ) : ℂ) * besselK (4 / 3 - 1) (A * v)) S :=
      hKi.mono_set hSI
    simp only [hg]
    rw [integral_sub hS3 (hSK.const_mul ρ), integral_const_mul, h2, sub_self]
  have hall : ∀ᵐ v ∂(volume.restrict (Ioi (0 : ℝ))), g v = 0 := by
    rw [Ioi_zero_eq_iUnion_Icc, ae_restrict_iUnion_iff]
    exact key
  filter_upwards [hall, ae_restrict_mem measurableSet_Ioi] with v hv hv0
  have hv0' : (0 : ℝ) < v := hv0
  have hvc : (v : ℂ) ≠ 0 := by exact_mod_cast hv0'.ne'
  simp only [hg] at hv
  rw [show (4 / 3 : ℂ) - 1 = 1 / 3 by norm_num] at hv
  have e3 : ((v ^ (-3 : ℤ) : ℝ) : ℂ) = ((v : ℂ) ^ 3)⁻¹ := by
    rw [Complex.ofReal_zpow, zpow_neg]
    norm_cast
  have e2 : ((v ^ (-2 : ℤ) : ℝ) : ℂ) = ((v : ℂ) ^ 2)⁻¹ := by
    rw [Complex.ofReal_zpow, zpow_neg]
    norm_cast
  rw [e3, e2] at hv
  field_simp at hv
  linear_combination hv

end Eis

end

#print axioms Eis.rowBd_finite
#print axioms Eis.row_mem_rowBd
#print axioms Eis.measurableSet_boxT
#print axioms Eis.cBox_ne_top
#print axioms Eis.tsum_boxT_le_of_siegel
#print axioms Eis.tsum_boxT_le
#print axioms Eis.measurableSet_boxZ
#print axioms Eis.cTr_ne_top
#print axioms Eis.tsum_boxZ_le
#print axioms Eis.lintegral_boxZ_lt_top
#print axioms Eis.measurable_thetaF
#print axioms Eis.memLp_thetaF
#print axioms Eis.enorm_thetaF_slAct
#print axioms Eis.lintegral_boxZ_thetaF_lt_top
#print axioms Eis.setLIntegral_volume_le
#print axioms Eis.integral_fundP3_conj_mul_of_int
#print axioms Eis.inner_pmSer_thetaL_unfold
#print axioms Eis.integrableOn_slice
#print axioms Eis.integrableOn_ebr_thetaF
#print axioms Eis.Ioi_zero_eq_iUnion_Icc
#print axioms Eis.coef_thetaF_ae
