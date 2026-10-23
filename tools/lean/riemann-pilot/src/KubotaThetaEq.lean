import KubotaThetaSeries

/-! # `θ̃ = S` almost everywhere, and three clauses of `KubotaTheta` (round 437)

S5f-10 of round 360's plan, part 20 (S5f-10f, tenth part). Round 436's next step planned `θ̃ = S` almost
everywhere, with `S` θ's Fourier series (round 436's `thS`), and `S` automorphic at every point. This round
proves both, for `r > 0` and `Y > 0`:

* **Square-integrable slices** (**`ae_lintegral_sq_slice_lt_top`** and **`ae_integrable_slice`**, with
  `thetaF_add_period`, `enorm_sub_sq_le` and `lintegral_sq_boxZ_thetaF_lt_top`): `∫_{box}|θ̃|² dz dv/v³ < ∞`
  (round 432's `lintegral_boxZ_lt_top` applied to `θ̃²`), so by Tonelli `∫_{3P}|θ̃(z, v)|² dz < ∞` for almost
  every `v > 0`; `θ̃` is periodic under `3ℤ[ω]` (round 425's automorphy at the translations).
* **`θ̃ = S` almost everywhere** (**`ae_ae_thetaF_eq_thS`** and **`ae_thetaF_eq_thS`**, with
  `continuous_thS_slice` and `exists_bound_thS_slice`): for almost every `v > 0`, `θ̃(·, v) − S(·, v)` is
  square-integrable on `3P` with vanishing Fourier coefficients (rounds 432, 433 and 436), so it vanishes
  almost everywhere (round 435's `ae_eq_zero_of_coef` and `ae_eq_zero_of_periodic`); then `θ̃ = S` almost
  everywhere on upper half-space (Mathlib's `Measure.prod_apply_symm`).
* **`S` is automorphic** (**`isAut_thS`**, with `continuousOn_slAct` and `ae_slAct`): `S(γp) = κ(γ)S(p)` for
  `γ ∈ Γ_1(3)` and every `p` in upper half-space, almost everywhere by round 425's `isAut_thetaF`, since the
  action preserves `dz dv/v³` (round 386's `lintegral_slAct`), and everywhere by continuity (Mathlib's
  `Measure.eqOn_open_of_ae_eq`).
* **Three clauses of `KubotaTheta`** (**`exists_theta_series`**, with `atG_thS`): a function equal to
  `thSer c₀ τ` at every point of upper half-space, with `τ` supported on `δ₃ℤ[ω]`, and automorphic on `Γ_1(3)`
  in the form of round 361's `KubotaTheta`, which agrees almost everywhere with `θ̃`.
-/

open MeasureTheory Set Filter NumberField Complex
open scoped ENNReal Topology MatrixGroups

noncomputable section

namespace Eis

/-- **`θ̃` is periodic under `3ℤ[ω]`**: round 425's automorphy at the translations `T_{3u}`, where Kubota's
character is `1` (round 426's `kub_slT`). -/
theorem thetaF_add_period (r Y : ℝ) (hY : 0 < Y) (z : ℂ) (u : 𝓞 K) {v : ℝ} (hv : 0 < v) :
    thetaF r Y hY (z + σO (3 * u), v) = thetaF r Y hY (z, v) := by
  have h := isAut_thetaF r Y hY (slT (3 * u)) (slT_mem_Gam3 (dvd_mul_right 3 u)) (z, v) hv
  simp only [slAct_slT, kub_slT, one_mul] at h
  exact h

theorem enorm_sub_sq_le (a b : ℂ) : ‖a - b‖ₑ ^ 2 ≤ 2 * (‖a‖ₑ ^ 2 + ‖b‖ₑ ^ 2) := by
  have h : ‖a - b‖₊ ^ 2 ≤ 2 * (‖a‖₊ ^ 2 + ‖b‖₊ ^ 2) :=
    (pow_le_pow_left₀ zero_le (nnnorm_sub_le a b) 2).trans add_sq_le
  have h' := ENNReal.coe_le_coe.2 h
  push_cast at h'
  simpa [enorm_eq_nnnorm] using h'

/-- **`|θ̃|²` on boxes**: `∫_{box}|θ̃|² dz dv/v³ < ∞` over `{|z| ≤ Z, α ≤ v ≤ β}` with `α > 0` (round 432's
`lintegral_boxZ_lt_top` applied to `θ̃²`). -/
theorem lintegral_sq_boxZ_thetaF_lt_top {r : ℝ} (hr : 0 < r) {Y : ℝ} (hY : 0 < Y) (Z : ℝ) {α : ℝ}
    (hα : 0 < α) (β : ℝ) : ∫⁻ p in boxZ Z α β, ‖thetaF r Y hY p‖ₑ ^ 2 ∂uhsMeasure < ⊤ := by
  have hL : ∫⁻ p, ‖thetaF r Y hY p ^ 2‖ₑ ∂(muR rhoG) < ⊤ := by
    simp only [enorm_pow]
    have h := lintegral_enorm_sq_lt_top (thetaL r Y hY)
    rwa [lintegral_congr_ae ((thetaL_ae_eq_thetaF hr hY).mono fun p hp => by rw [hp])] at h
  have hu := lintegral_boxZ_lt_top (u := fun p => thetaF r Y hY p ^ 2)
    ((measurable_thetaF r Y hY).pow_const 2)
    (fun γ hγ p hp => by simp only [enorm_pow]; rw [enorm_thetaF_slAct r Y hY γ hγ p hp]) hL Z hα β
  simpa only [enorm_pow] using hu

/-- **`|θ̃|²` on almost every slice**: `∫_{3P}|θ̃(z, v)|² dz < ∞` for almost every `v > 0`. -/
theorem ae_lintegral_sq_slice_lt_top {r : ℝ} (hr : 0 < r) {Y : ℝ} (hY : 0 < Y) :
    ∀ᵐ v ∂(volume.restrict (Ioi (0 : ℝ))), ∫⁻ z in fundP3, ‖thetaF r Y hY (z, v)‖ₑ ^ 2 < ⊤ := by
  rw [Ioi_zero_eq_iUnion_Icc, ae_restrict_iUnion_iff]
  intro n
  obtain ⟨α, hαd⟩ : ∃ α : ℝ, α = 1 / ((n : ℝ) + 1) := ⟨_, rfl⟩
  obtain ⟨β, hβd⟩ : ∃ β : ℝ, β = (n : ℝ) + 1 := ⟨_, rfl⟩
  rw [← hαd, ← hβd]
  have hα : 0 < α := by rw [hαd]; positivity
  have hF : Measurable fun p : ℂ × ℝ => ‖thetaF r Y hY p‖ₑ ^ 2 :=
    (measurable_thetaF r Y hY).enorm.pow_const 2
  have hT : MeasurableSet (fundP3 ×ˢ Icc α β) := measurableSet_fundP3.prod measurableSet_Icc
  have hbox : ∫⁻ p in fundP3 ×ˢ Icc α β, ‖thetaF r Y hY p‖ₑ ^ 2 < ⊤ := by
    refine (setLIntegral_volume_le hF hT hα (fun p hp => ⟨hp.2.1, hp.2.2⟩)).trans_lt
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_)
    refine (lintegral_mono_set fun p hp => ?_).trans_lt (lintegral_sq_boxZ_thetaF_lt_top hr hY 6 hα β)
    obtain ⟨hp1, hp2⟩ := Set.mem_prod.1 hp
    exact ⟨norm_le_six_of_mem_fundP3 hp1, hp2.1, hp2.2⟩
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict, lintegral_prod_symm _ hF.aemeasurable] at hbox
  exact ae_lt_top' (hF.lintegral_prod_left' (μ := volume.restrict fundP3)).aemeasurable hbox.ne

/-- `θ̃` is integrable on almost every slice `3P × {v}`, `v > 0` (round 433's `integrableOn_thetaF`). -/
theorem ae_integrable_slice {r : ℝ} (hr : 0 < r) {Y : ℝ} (hY : 0 < Y) :
    ∀ᵐ v ∂(volume.restrict (Ioi (0 : ℝ))),
      Integrable (fun z => thetaF r Y hY (z, v)) (volume.restrict fundP3) := by
  rw [Ioi_zero_eq_iUnion_Icc, ae_restrict_iUnion_iff]
  intro n
  have hα : 0 < 1 / ((n : ℝ) + 1) := by positivity
  have h := integrableOn_thetaF hr hY hα ((n : ℝ) + 1)
  have h' : Integrable (thetaF r Y hY)
      ((volume.restrict fundP3).prod (volume.restrict (Icc (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1)))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact h
  exact h'.prod_left_ae

theorem continuous_thS_slice {r : ℝ} (hr : 0 < r) {Y : ℝ} (hY : 0 < Y) {v : ℝ} (hv : 0 < v) :
    Continuous fun z : ℂ => thS r Y hY (z, v) :=
  (continuousOn_thS hr hY).comp_continuous (continuous_id.prodMk continuous_const) fun _ => hv

theorem exists_bound_thS_slice {r : ℝ} (hr : 0 < r) {Y : ℝ} (hY : 0 < Y) {v : ℝ} (hv : 0 < v) :
    ∃ M : ℝ, ∀ z ∈ fundP3, ‖thS r Y hY (z, v)‖ ≤ M := by
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) 6).exists_bound_of_continuousOn
    (continuous_thS_slice hr hY hv).continuousOn
  exact ⟨M, fun z hz => hM z (mem_closedBall_zero_iff.2 (norm_le_six_of_mem_fundP3 hz))⟩

/-- **`θ̃ = S` on almost every slice**: for almost every `v > 0`, `θ̃(z, v) = S(z, v)` for almost every
`z ∈ ℂ`, by round 435's uniqueness of Fourier coefficients. -/
theorem ae_ae_thetaF_eq_thS {r : ℝ} (hr : 0 < r) {Y : ℝ} (hY : 0 < Y) :
    ∀ᵐ v ∂(volume.restrict (Ioi (0 : ℝ))), ∀ᵐ z, thetaF r Y hY (z, v) = thS r Y hY (z, v) := by
  have : Countable (𝓞 K) := crdEquiv.symm.injective.countable
  have hcoef : ∀ᵐ v ∂(volume.restrict (Ioi (0 : ℝ))), ∀ x : 𝓞 K, x ≠ 0 →
      ∫ z in fundP3, ebr (-(σO (δ3 * x) / 9 * z)) * thetaF r Y hY (z, v) =
        rhoM x r Y hY * ((v : ℂ) * besselK (1 / 3) (4 * Real.pi * ‖σO (δ3 * x) / 9‖ * v)) := by
    refine ae_all_iff.2 fun x => ?_
    by_cases hx : x = 0
    · exact ae_of_all _ fun v h => absurd hx h
    · filter_upwards [coef_thetaF_ae hx hr hY] with v hv _ using hv
  filter_upwards [hcoef, const_thetaF_ae hr hY, ae_lintegral_sq_slice_lt_top hr hY,
    ae_integrable_slice hr hY, ae_restrict_mem measurableSet_Ioi] with v hc hc0 h2 hi hv
  have hv' : (0 : ℝ) < v := hv
  have hfin : IsFiniteMeasure (volume.restrict fundP3) :=
    isFiniteMeasure_restrict.2 (by rw [volume_fundP3]; exact ENNReal.ofReal_ne_top)
  have hSc := continuous_thS_slice hr hY hv'
  have hθm : Measurable fun z : ℂ => thetaF r Y hY (z, v) :=
    (measurable_thetaF r Y hY).comp (measurable_id.prodMk measurable_const)
  obtain ⟨M, hM⟩ := exists_bound_thS_slice hr hY hv'
  have hSi : Integrable (fun z => thS r Y hY (z, v)) (volume.restrict fundP3) :=
    (integrable_const M).mono' hSc.aestronglyMeasurable
      (ae_restrict_of_forall_mem measurableSet_fundP3 fun z hz => hM z hz)
  have hS2 : ∫⁻ z in fundP3, ‖thS r Y hY (z, v)‖ₑ ^ 2 < ⊤ := by
    calc ∫⁻ z in fundP3, ‖thS r Y hY (z, v)‖ₑ ^ 2
        ≤ ∫⁻ _ in fundP3, ENNReal.ofReal M ^ 2 :=
          setLIntegral_mono measurable_const fun z hz => by
            gcongr
            rw [← ofReal_norm]
            exact ENNReal.ofReal_le_ofReal (hM z hz)
      _ < ⊤ := by
          rw [setLIntegral_const, volume_fundP3]
          exact ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofReal_lt_top) ENNReal.ofReal_lt_top
  obtain ⟨g, hgdef⟩ : ∃ g : ℂ → ℂ, g = fun z => thetaF r Y hY (z, v) - thS r Y hY (z, v) := ⟨_, rfl⟩
  have hgm : Measurable g := by rw [hgdef]; exact hθm.sub hSc.measurable
  have hg2 : ∫⁻ z in fundP3, ‖g z‖ₑ ^ 2 < ⊤ := by
    have hm1 : Measurable fun z : ℂ => ‖thetaF r Y hY (z, v)‖ₑ ^ 2 := hθm.enorm.pow_const 2
    calc ∫⁻ z in fundP3, ‖g z‖ₑ ^ 2
        ≤ ∫⁻ z in fundP3, 2 * (‖thetaF r Y hY (z, v)‖ₑ ^ 2 + ‖thS r Y hY (z, v)‖ₑ ^ 2) :=
          lintegral_mono fun z => by rw [hgdef]; exact enorm_sub_sq_le _ _
      _ = 2 * ((∫⁻ z in fundP3, ‖thetaF r Y hY (z, v)‖ₑ ^ 2) +
            ∫⁻ z in fundP3, ‖thS r Y hY (z, v)‖ₑ ^ 2) := by
          rw [lintegral_const_mul' _ _ (by norm_num), lintegral_add_left hm1]
      _ < ⊤ := ENNReal.mul_lt_top (by norm_num) (ENNReal.add_lt_top.2 ⟨h2, hS2⟩)
  have hgc : ∀ x : 𝓞 K, ∫ z in fundP3, ebr (-(σO (δ3 * x) / 9 * z)) * g z = 0 := by
    intro x
    have hEc : Continuous fun z : ℂ => ebr (-(σO (δ3 * x) / 9 * z)) := by unfold ebr; fun_prop
    have hbd : ∀ᵐ z ∂(volume.restrict fundP3), ‖ebr (-(σO (δ3 * x) / 9 * z))‖ ≤ 1 :=
      ae_of_all _ fun z => (norm_ebr _).le
    have e : (fun z => ebr (-(σO (δ3 * x) / 9 * z)) * g z) = fun z =>
        ebr (-(σO (δ3 * x) / 9 * z)) * thetaF r Y hY (z, v) -
          ebr (-(σO (δ3 * x) / 9 * z)) * thS r Y hY (z, v) := by
      funext z; rw [hgdef, mul_sub]
    rw [e, integral_sub (hi.bdd_mul hEc.aestronglyMeasurable hbd)
      (hSi.bdd_mul hEc.aestronglyMeasurable hbd), sub_eq_zero]
    by_cases hx : x = 0
    · subst hx
      simp only [mul_zero, map_zero, zero_div, zero_mul, neg_zero, ebr_zero, one_mul]
      rw [hc0, integral_thS hr hY hv']
    · rw [hc x hx, integral_ebr_thS hr hY hx hv']
  have hper : ∀ z u, g (z + σO (3 * u)) = g z := fun z u => by
    rw [hgdef]
    simp only [thetaF_add_period r Y hY z u hv', thS_add_period]
  filter_upwards [ae_eq_zero_of_periodic hgm hper (ae_eq_zero_of_coef hgm hg2 hgc)] with z hz
  rw [hgdef] at hz
  exact sub_eq_zero.1 hz

/-- **`θ̃ = S` almost everywhere on upper half-space**: the automorphic representative of θ (round 425's
`thetaF`) agrees almost everywhere with its Fourier series. -/
theorem ae_thetaF_eq_thS {r : ℝ} (hr : 0 < r) {Y : ℝ} (hY : 0 < Y) :
    ∀ᵐ p ∂(volume.restrict UHS), thetaF r Y hY p = thS r Y hY p := by
  classical
  obtain ⟨S', hS'⟩ : ∃ S' : ℂ × ℝ → ℂ, S' = UHS.piecewise (thS r Y hY) 0 := ⟨_, rfl⟩
  have hS'm : Measurable S' := by
    rw [hS']
    exact (continuousOn_thS hr hY).measurable_piecewise continuousOn_const measurableSet_UHS
  have hNm : MeasurableSet {p : ℂ × ℝ | thetaF r Y hY p ≠ S' p} :=
    (measurableSet_eq_fun (measurable_thetaF r Y hY) hS'm).compl
  have hUHS : UHS = (univ : Set ℂ) ×ˢ Ioi (0 : ℝ) := by
    ext p
    simp [UHS]
  have hμ : volume.restrict UHS = (volume : Measure ℂ).prod (volume.restrict (Ioi (0 : ℝ))) := by
    rw [hUHS, Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]
  have h0 : (volume.restrict UHS) {p : ℂ × ℝ | thetaF r Y hY p ≠ S' p} = 0 := by
    rw [hμ, Measure.prod_apply_symm hNm]
    rw [lintegral_congr_ae (g := fun _ => (0 : ℝ≥0∞)) ?_, lintegral_zero]
    filter_upwards [ae_ae_thetaF_eq_thS hr hY, ae_restrict_mem measurableSet_Ioi] with v hv hv0
    have e : (fun z : ℂ => (z, v)) ⁻¹' {p : ℂ × ℝ | thetaF r Y hY p ≠ S' p} =
        {z | ¬ thetaF r Y hY (z, v) = thS r Y hY (z, v)} := by
      ext z
      have hz : (z, v) ∈ UHS := show (0 : ℝ) < v from hv0
      show thetaF r Y hY (z, v) ≠ S' (z, v) ↔ ¬thetaF r Y hY (z, v) = thS r Y hY (z, v)
      rw [hS', Set.piecewise_eq_of_mem _ _ _ hz]
    rw [e]
    exact ae_iff.1 hv
  filter_upwards [(ae_iff.2 (by simpa using h0) : ∀ᵐ p ∂(volume.restrict UHS), thetaF r Y hY p = S' p),
    ae_restrict_mem measurableSet_UHS] with p hp hpU
  rw [hp, hS', Set.piecewise_eq_of_mem _ _ _ hpU]

/-! ### `S` is automorphic -/

/-- The action of `SL_2(ℤ[ω])` is continuous on upper half-space. -/
theorem continuousOn_slAct (γ : SL(2, 𝓞 K)) : ContinuousOn (slAct γ) UHS := by
  intro p hp
  have hD := slDen_pos γ hp
  refine ContinuousAt.continuousWithinAt ?_
  have hDc : Continuous fun q : ℂ × ℝ => uhsDen (σO (γ 1 0)) (σO (γ 1 1)) q.1 q.2 := by
    unfold uhsDen; fun_prop
  show ContinuousAt (fun q : ℂ × ℝ => (uhsZ (σO (γ 0 0)) (σO (γ 0 1)) (σO (γ 1 0)) (σO (γ 1 1)) q.1 q.2,
    uhsV (σO (γ 1 0)) (σO (γ 1 1)) q.1 q.2)) p
  refine ContinuousAt.prodMk ?_ ?_
  · unfold uhsZ
    refine ContinuousAt.div (by fun_prop) (Complex.continuous_ofReal.continuousAt.comp hDc.continuousAt) ?_
    exact_mod_cast hD.ne'
  · unfold uhsV
    exact continuousAt_snd.div hDc.continuousAt hD.ne'

/-- **Almost-everywhere statements on upper half-space pass through the action**, which preserves
`dz dv/v³` (round 386's `lintegral_slAct`), a measure with the null sets of `dz dv` there. -/
theorem ae_slAct {s : Set (ℂ × ℝ)} (hs : MeasurableSet s) (h : ∀ᵐ q ∂(volume.restrict UHS), q ∈ s)
    (γ : SL(2, 𝓞 K)) : ∀ᵐ q ∂(volume.restrict UHS), slAct γ q ∈ s := by
  have hW : volume.restrict UHS ≪ uhsMeasure := by
    refine withDensity_absolutelyContinuous' measurable_uhsW.aemeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_UHS] with q hq
    have hq' : (0 : ℝ) < q.2 := hq
    unfold uhsW
    exact (ENNReal.ofReal_pos.2 (zpow_pos hq' _)).ne'
  have hs0 : (volume.restrict UHS) sᶜ = 0 := by
    rw [ae_iff] at h
    exact h
  have h0 : uhsMeasure sᶜ = 0 := withDensity_absolutelyContinuous _ _ hs0
  have h1 : uhsMeasure (slAct γ ⁻¹' sᶜ) = 0 := by
    have e := lintegral_slAct γ (F := sᶜ.indicator (1 : ℂ × ℝ → ℝ≥0∞))
      (measurable_one.indicator hs.compl)
    rw [lintegral_indicator_one hs.compl, h0] at e
    rw [← lintegral_indicator_one ((measurable_slAct γ) hs.compl), ← e]
    exact lintegral_congr fun q => rfl
  exact ae_iff.2 (hW h1)

/-- **`S` is automorphic at every point**: `S(γp) = κ(γ)S(p)` for `γ ∈ Γ_1(3)` and every `p` in upper
half-space, from round 425's `isAut_thetaF`, `θ̃ = S` almost everywhere, and continuity. -/
theorem isAut_thS {r : ℝ} (hr : 0 < r) {Y : ℝ} (hY : 0 < Y) :
    IsAut Gam3 (fun g => kub ↑g) (thS r Y hY) := by
  classical
  intro γ hγ p hp
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
  have hae : ∀ᵐ q ∂(volume.restrict UHS), thS r Y hY (slAct γ q) = kub ↑γ * thS r Y hY q := by
    filter_upwards [hS'ae, ae_slAct hset hS'ae γ, ae_restrict_mem measurableSet_UHS] with q hq1 hq2 hqU
    have hq1' : thetaF r Y hY q = thS r Y hY q := by
      have := hq1
      simp only [hS', Set.piecewise_eq_of_mem _ _ _ hqU] at this
      exact this
    have hq2' : thetaF r Y hY (slAct γ q) = thS r Y hY (slAct γ q) := by
      have := hq2
      simp only [hS', Set.piecewise_eq_of_mem _ _ _ (slAct_mem γ hqU)] at this
      exact this
    rw [← hq2', isAut_thetaF r Y hY γ hγ q hqU, hq1']
  have hU : IsOpen UHS := isOpen_lt continuous_const continuous_snd
  have hc1 : ContinuousOn (fun q => thS r Y hY (slAct γ q)) UHS :=
    (continuousOn_thS hr hY).comp (continuousOn_slAct γ) fun q hq => slAct_mem γ hq
  have hc2 : ContinuousOn (fun q => kub ↑γ * thS r Y hY q) UHS :=
    continuousOn_const.mul (continuousOn_thS hr hY)
  exact Measure.eqOn_open_of_ae_eq hae hU hc1 hc2 hp

/-! ### Three clauses of `KubotaTheta` -/

/-- **The automorphy clause of round 361's `KubotaTheta` for `S`**: for `γ ≡ I (mod 3)` of determinant `1`,
`S(γ(z + vj)) = κ(γ)·S(z + vj)` for `v > 0`, in round 361's notation `atG`. -/
theorem atG_thS {r : ℝ} (hr : 0 < r) {Y : ℝ} (hY : 0 < Y) (γ : Matrix (Fin 2) (Fin 2) (𝓞 K))
    (hdet : γ.det = 1) (h3 : ModThree γ) (z : ℂ) {v : ℝ} (hv : 0 < v) :
    atG (fun z v => thS r Y hY (z, v)) (γ.map σO) z v = kub γ * thS r Y hY (z, v) := by
  have hγ : (⟨γ, hdet⟩ : SL(2, 𝓞 K)) ∈ Gam3 := mem_Gam3.2 h3
  have h := isAut_thS hr hY ⟨γ, hdet⟩ hγ (z, v) hv
  exact h

/-- **Three clauses of round 361's `KubotaTheta`**, for θ's Fourier series: a function on upper half-space,
equal to a theta-type series `thSer c₀ τ` at every point, with `τ` supported on `δ₃ℤ[ω]`, and automorphic
on `Γ_1(3)` with Kubota's character; it agrees almost everywhere with θ's representative (round 425's
`thetaF`). -/
theorem exists_theta_series {r : ℝ} (hr : 0 < r) {Y : ℝ} (hY : 0 < Y) :
    ∃ (θ : ℂ → ℝ → ℂ) (c₀ : ℂ) (τ : 𝓞 K → ℂ),
      (∀ z v, 0 < v → θ z v = thSer c₀ τ z v) ∧ (∀ m, τ m ≠ 0 → δ3 ∣ m) ∧
      (∀ γ : Matrix (Fin 2) (Fin 2) (𝓞 K), γ.det = 1 → ModThree γ → ∀ z v, 0 < v →
        atG θ (γ.map σO) z v = kub γ * θ z v) ∧
      ∀ᵐ p ∂(volume.restrict UHS), thetaF r Y hY p = θ p.1 p.2 :=
  ⟨fun z v => thS r Y hY (z, v), phiG (4 / 3) / 3, tauTh r Y hY, fun _ _ _ => rfl,
    fun _ h => dvd_of_tauTh_ne_zero h, fun γ hdet h3 z _ hv => atG_thS hr hY γ hdet h3 z hv,
    ae_thetaF_eq_thS hr hY⟩

end Eis

end

#print axioms Eis.thetaF_add_period
#print axioms Eis.enorm_sub_sq_le
#print axioms Eis.lintegral_sq_boxZ_thetaF_lt_top
#print axioms Eis.ae_lintegral_sq_slice_lt_top
#print axioms Eis.ae_integrable_slice
#print axioms Eis.continuous_thS_slice
#print axioms Eis.exists_bound_thS_slice
#print axioms Eis.ae_ae_thetaF_eq_thS
#print axioms Eis.ae_thetaF_eq_thS
#print axioms Eis.continuousOn_slAct
#print axioms Eis.ae_slAct
#print axioms Eis.isAut_thS
#print axioms Eis.atG_thS
#print axioms Eis.exists_theta_series
