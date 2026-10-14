import KubotaUnfoldEis
import KubotaPhiPole

/-! # The pairing with pseudo-Eisenstein series, and θ ≠ 0 (round 427)

S5f-10 of round 360's plan, part 10 (S5f-10e, third part). Round 426's next step planned the constant term of
`E_s − h_s` high in the cusp, the identity theorem, and θ ≠ 0. This round proves them, for `R = 2cosh r − 2`
with `r > 0`, `Y > 0`, `ν = ρ_G dμ` as in round 423, and a profile `ψ` measurable and bounded, vanishing
outside `[α, β]` with `α ≥ Y` and `Yα > 1`:

* **High in the cusp** (**`eisHigh_eq`**, **`norm_eisLow_le`** and **`integral_fundP3_eisLow`**, with
  `height_le_inv`, `eisLow_eq_sub` and `one_lt_of_Y_le`): for `v ≥ Y` with `Yv > 1`, `h_s(z, v) = v^s`, since
  the row `(0, 1)` has height `v` and a bottom row with `c ≠ 0` has height at most `1/v < Y`. So
  `|E_s − h_s| ≤ cuspC(σ)·v^{2−σ}` there for `σ = Re s > 2` (round 388's `norm_eis1_sub_le`), and
  `∫_{3P} (E_s − h_s)(z, v) dz = (9√3/2)·φ(s)v^{2−s}` (round 389's `constTerm_eis1`).
* **The pairing for `Re s > 2`** (**`integral_conj_eisLow`** and **`inner_pseis_uL`**, with
  `cpow_neg_one_sub`, `uhsMeasure_fundP3_Icc_lt_top`, `lintegral_rhoT3_eisLow_ne_top` and `memLp_pseis_Icc`):
  by round 426's `inner_toLp_pseis` and Fubini, `⟨E(ψ), ũ_s⟩ = (9√3/2)·φ(s)·M_ψ(s)` with
  `M_ψ(s) = ∫_0^∞ conj ψ(v)v^{−1−s} dv`, for `Re s > 2` with `Im ĥ(s) ≠ 0` (round 424's `uL_eq_eisLow`).
* **The identity theorem and the limit** (`mellinPsi` and `domU`, definitions; **`differentiable_mellinPsi`**
  and **`inner_pseis_thetaL`**, with `mellinPsi_eq`, `isOpen_domU` and `convex_domU`): `M_ψ` is entire
  (Mathlib's `mellin_differentiableAt_of_isBigO_rpow`). Both sides are holomorphic on the convex open set
  `{Re s > 1, 0 < Im s < π/r}` (round 418's `im_hhat_pos`, round 424's `differentiableAt_inner_uL`, round
  417's `differentiableAt_phiC`) and agree where `Re s > 2` (round 416's `eisPhi_eq_phiC`), so they agree on
  the whole set (Mathlib's `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`). Multiplying by `iε` at
  `s = 4/3 + iε` and letting `ε → 0⁺` (round 425's `tendsto_uL_thetaL`, round 417's `tendsto_phiC_residue`)
  gives `⟨E(ψ), θ⟩ = (9√3/2)·Res φ·M_ψ(4/3)`, with `Res φ = phiG(4/3)/3`.
* **θ ≠ 0** (**`thetaL_ne_zero`**, with `mellinPsi_indicator_ne_zero`): for `ψ = 1_{[α, α + 1]}` with
  `α = Y + 1/Y`, `M_ψ(4/3) = ∫_α^{α+1} v^{−7/3} dv > 0`, and `Res φ ≠ 0` (round 417's `phiRes_ne_zero`).
-/

open MeasureTheory Set Filter NumberField Complex Ideal
open scoped ENNReal Topology MatrixGroups ComplexConjugate

noncomputable section

namespace Eis

/-! ### High in the cusp -/

/-- **A bottom row with `c ≠ 0` has height at most `1/v`**: `v/(|cz + d|² + |c|²v²) ≤ 1/v`. -/
theorem height_le_inv {c : 𝓞 K} (hc : c ≠ 0) (d : 𝓞 K) (z : ℂ) {v : ℝ} (hv : 0 < v) :
    v / uhsDen (σO c) (σO d) z v ≤ 1 / v := by
  have h1 : 1 ≤ ‖σO c‖ := one_le_norm_σO hc
  have h2 : 1 ≤ Complex.normSq (σO c) := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith
  have hD : v ^ 2 ≤ uhsDen (σO c) (σO d) z v := by
    unfold uhsDen
    nlinarith [Complex.normSq_nonneg (σO c * z + σO d), sq_nonneg v]
  have hv2 : 0 < v ^ 2 := by positivity
  rw [div_le_div_iff₀ (lt_of_lt_of_le hv2 hD) hv]
  nlinarith

/-- **`h_s = v^s` high in the cusp**: for `Y > 0`, `v ≥ Y` and `Yv > 1`, the only term of `h_s(z, v)` is that
of the row `(0, 1)`. -/
theorem eisHigh_eq (s : ℂ) {Y : ℝ} (hY : 0 < Y) {p : ℂ × ℝ} (hYv : Y ≤ p.2) (h1 : 1 < Y * p.2) :
    eisHigh s Y p = ((p.2 : ℝ) : ℂ) ^ s := by
  have hv : 0 < p.2 := lt_of_lt_of_le hY hYv
  have hb : BRow ((0 : 𝓞 K), (1 : 𝓞 K)) := bRow_zero_iff.2 rfl
  unfold eisHigh pseis
  rw [tsum_eq_single ((0 : 𝓞 K), (1 : 𝓞 K)) fun cd hcd => ?_]
  · unfold psTerm
    simp only [hb, ↓reduceIte]
    change σO (cub 0 (span {1})) * highF s Y (p.2 / uhsDen (σO 0) (σO 1) p.1 p.2) = _
    have hD : uhsDen (σO 0) (σO 1) p.1 p.2 = 1 := by
      unfold uhsDen
      simp
    rw [hD, div_one, cub_one_right, map_one, one_mul]
    unfold highF
    simp only [show ¬ p.2 < Y from not_lt.2 hYv, ↓reduceIte]
  · unfold psTerm
    split_ifs with hb'
    · have hc : cd.1 ≠ 0 := by
        intro h0
        apply hcd
        obtain ⟨c, d⟩ := cd
        simp only at h0
        subst h0
        rw [bRow_zero_iff.1 hb']
      have hlt : p.2 / uhsDen (σO cd.1) (σO cd.2) p.1 p.2 < Y :=
        lt_of_le_of_lt (height_le_inv hc cd.2 p.1 hv) (by rw [div_lt_iff₀ hv]; linarith)
      unfold highF
      simp only [hlt, ↓reduceIte, mul_zero]
    · rfl

/-- **`E_s − h_s = E_s − v^s` high in the cusp**, for `Re s > 2`, `Y > 0`, `v ≥ Y` and `Yv > 1`. -/
theorem eisLow_eq_sub {s : ℂ} (hs : 2 < s.re) {Y : ℝ} (hY : 0 < Y) {p : ℂ × ℝ} (hYv : Y ≤ p.2)
    (h1 : 1 < Y * p.2) : eisLow s Y p = eis1 s p - ((p.2 : ℝ) : ℂ) ^ s := by
  have hp : p ∈ UHS := show 0 < p.2 from lt_of_lt_of_le hY hYv
  rw [eis1_eq_eisLow_add_eisHigh hs Y hp, eisHigh_eq s hY hYv h1, add_sub_cancel_right]

theorem one_lt_of_Y_le {Y v : ℝ} (hY : 0 < Y) (hYv : Y ≤ v) (h1 : 1 < Y * v) : 1 < v := by
  have hv : 0 < v := lt_of_lt_of_le hY hYv
  nlinarith [mul_le_mul_of_nonneg_right hYv hv.le]

/-- **`E_s − h_s` is bounded high in the cusp**: `|E_s − h_s| ≤ cuspC(σ)·v^{2−σ}` for `σ = Re s > 2`, `Y > 0`,
`v ≥ Y` and `Yv > 1` (round 388's `norm_eis1_sub_le`). -/
theorem norm_eisLow_le {s : ℂ} (hs : 2 < s.re) {Y : ℝ} (hY : 0 < Y) {p : ℂ × ℝ} (hYv : Y ≤ p.2)
    (h1 : 1 < Y * p.2) : ‖eisLow s Y p‖ ≤ cuspC s.re * p.2 ^ (2 - s.re) := by
  rw [eisLow_eq_sub hs hY hYv h1]
  exact norm_eis1_sub_le hs (by linarith [one_lt_of_Y_le hY hYv h1])

/-! ### The period integral -/

/-- **The period integral of `E_s − h_s` high in the cusp**:
`∫_{3P} (E_s − h_s)(z, v) dz = (9√3/2)·φ(s)v^{2−s}` for `Re s > 2`, `Y > 0`, `v ≥ Y` and `Yv > 1` (round 389's
`constTerm_eis1`). -/
theorem integral_fundP3_eisLow {s : ℂ} (hs : 2 < s.re) {Y : ℝ} (hY : 0 < Y) {v : ℝ} (hYv : Y ≤ v)
    (h1 : 1 < Y * v) :
    ∫ z in fundP3, eisLow s Y (z, v) =
      ((9 * (Real.sqrt 3 / 2) : ℝ) : ℂ) * eisPhi s * ((v : ℝ) : ℂ) ^ (2 - s) := by
  have hv : 0 < v := lt_of_lt_of_le hY hYv
  have hfin : volume fundP3 ≠ ⊤ := by rw [volume_fundP3]; exact ENNReal.ofReal_ne_top
  have hm : Measurable fun z : ℂ => eisLow s Y (z, v) :=
    (measurable_eisLow s Y).comp (measurable_id.prodMk measurable_const)
  have hI : IntegrableOn (fun z => eisLow s Y (z, v)) fundP3 :=
    Measure.integrableOn_of_bounded (M := cuspC s.re * v ^ (2 - s.re)) hfin hm.aestronglyMeasurable
      (Eventually.of_forall fun z => norm_eisLow_le hs hY (p := (z, v)) hYv h1)
  have hC : IntegrableOn (fun _ : ℂ => ((v : ℝ) : ℂ) ^ s) fundP3 := integrableOn_const hfin
  have h2 : ∫ z in fundP3, eis1 s (z, v) =
      (∫ z in fundP3, eisLow s Y (z, v)) + ∫ z in fundP3, ((v : ℝ) : ℂ) ^ s := by
    rw [← integral_add hI hC]
    refine setIntegral_congr_fun measurableSet_fundP3 fun z _ => ?_
    rw [eisLow_eq_sub hs hY (p := (z, v)) hYv h1]
    ring
  have h3 := constTerm_eis1 hs hv
  have h9 : (((9 * (Real.sqrt 3 / 2) : ℝ) : ℂ)) ≠ 0 := by
    have : (0 : ℝ) < 9 * (Real.sqrt 3 / 2) := by positivity
    exact_mod_cast this.ne'
  rw [setIntegral_const, Measure.real, volume_fundP3, ENNReal.toReal_ofReal (by positivity),
    Complex.real_smul] at h2
  have h4 : ∫ z in fundP3, eis1 s (z, v) = ((9 * (Real.sqrt 3 / 2) : ℝ) : ℂ) *
      (((v : ℝ) : ℂ) ^ s + eisPhi s * ((v : ℝ) : ℂ) ^ (2 - s)) := by
    rw [← h3]
    field_simp
  rw [h4] at h2
  linear_combination -h2

/-! ### The pairing for `Re s > 2` -/

theorem cpow_neg_one_sub {v : ℝ} (hv : 0 < v) (s : ℂ) :
    ((v ^ (-3 : ℤ) : ℝ) : ℂ) * ((v : ℝ) : ℂ) ^ (2 - s) = ((v : ℝ) : ℂ) ^ (-1 - s) := by
  have hv' : ((v : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hv.ne'
  rw [Complex.ofReal_zpow, ← Complex.cpow_intCast, ← Complex.cpow_add _ _ hv']
  congr 1
  push_cast
  ring

/-- **`ν_{ρ_3}`-finiteness above height `α > 1`**: `μ(3P × [α, β]) < ∞`. -/
theorem uhsMeasure_fundP3_Icc_lt_top {α β : ℝ} (hα : 1 ≤ α) :
    uhsMeasure (fundP3 ×ˢ Icc α β) < ⊤ := by
  have hT : MeasurableSet (fundP3 ×ˢ Icc α β) := measurableSet_fundP3.prod measurableSet_Icc
  rw [uhsMeasure, withDensity_apply _ hT]
  calc ∫⁻ p in fundP3 ×ˢ Icc α β, uhsW p ∂(volume.restrict UHS)
      ≤ ∫⁻ _ in fundP3 ×ˢ Icc α β, 1 ∂(volume.restrict UHS) := by
        refine setLIntegral_mono measurable_const fun p hp => ?_
        have hv : 1 ≤ p.2 := hα.trans hp.2.1
        unfold uhsW
        exact ENNReal.ofReal_le_one.2 (zpow_le_one_of_nonpos₀ hv (by norm_num))
    _ = (volume.restrict UHS) (fundP3 ×ˢ Icc α β) := setLIntegral_one _
    _ ≤ volume (fundP3 ×ˢ Icc α β) := Measure.restrict_apply_le _ _
    _ < ⊤ := by
        rw [Measure.volume_eq_prod, Measure.prod_prod, volume_fundP3, Real.volume_Icc]
        exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top

/-- **The unfolded pairing for `Re s > 2`**: for `ψ` measurable, bounded and vanishing outside `[α, β]`, with
`Y > 0`, `α ≥ Y` and `Yα > 1`,
`∫_{3P×(0,∞)} conj ψ(v)·(E_s − h_s)(z, v) dz dv/v³ = (9√3/2)·φ(s)·∫_0^∞ conj ψ(v)v^{−1−s} dv`. -/
theorem integral_conj_eisLow {ψ : ℝ → ℂ} (hψ : Measurable ψ) {M α β : ℝ} (hM : ∀ v, ‖ψ v‖ ≤ M)
    (hψ0 : ∀ v, v ∉ Icc α β → ψ v = 0) {Y : ℝ} (hY : 0 < Y) (hYα : Y ≤ α) (h1 : 1 < Y * α) {s : ℂ}
    (hs : 2 < s.re) :
    ∫ p in Prod.fst ⁻¹' fundP3, conj (ψ p.2) * eisLow s Y p ∂uhsMeasure =
      ((9 * (Real.sqrt 3 / 2) : ℝ) : ℂ) * eisPhi s *
        ∫ v in Ioi 0, conj (ψ v) * ((v : ℝ) : ℂ) ^ (-1 - s) := by
  have hα : 0 < α := lt_of_lt_of_le hY hYα
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  set T : Set (ℂ × ℝ) := fundP3 ×ˢ Icc α β with hTdef
  set H : ℂ × ℝ → ℂ := fun q => ((q.2 ^ (-3 : ℤ) : ℝ) : ℂ) * (conj (ψ q.2) * eisLow s Y q) with hHdef
  have hT : MeasurableSet T := measurableSet_fundP3.prod measurableSet_Icc
  have hHm : Measurable H := by
    have : Measurable fun q : ℂ × ℝ => ((q.2 ^ (-3 : ℤ) : ℝ) : ℂ) := by fun_prop
    exact this.mul ((Complex.continuous_conj.measurable.comp (hψ.comp measurable_snd)).mul
      (measurable_eisLow s Y))
  have hbound : ∀ q ∈ T, ‖H q‖ ≤ M * cuspC s.re := by
    intro q hq
    have hv : α ≤ q.2 := hq.2.1
    have hYv : Y ≤ q.2 := hYα.trans hv
    have h1' : 1 < Y * q.2 := lt_of_lt_of_le h1 (mul_le_mul_of_nonneg_left hv hY.le)
    have hv1 : 1 ≤ q.2 := (one_lt_of_Y_le hY hYv h1').le
    have hv0 : 0 < q.2 := by linarith
    simp only [hHdef]
    rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity)]
    have hz : q.2 ^ (-3 : ℤ) ≤ 1 := zpow_le_one_of_nonpos₀ hv1 (by norm_num)
    have hE : ‖eisLow s Y q‖ ≤ cuspC s.re := by
      refine (norm_eisLow_le hs hY hYv h1').trans ?_
      have h5 : q.2 ^ (2 - s.re) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hv1 (by linarith)
      have hc := cuspC_nonneg (by linarith : 1 < s.re)
      nlinarith
    calc q.2 ^ (-3 : ℤ) * (‖ψ q.2‖ * ‖eisLow s Y q‖) ≤ 1 * (M * cuspC s.re) :=
          mul_le_mul hz (mul_le_mul (hM _) hE (norm_nonneg _) hM0) (by positivity) zero_le_one
      _ = M * cuspC s.re := one_mul _
  -- step 1: to Lebesgue measure on `ℂ × ℝ`
  have hstep1 : ∫ p in Prod.fst ⁻¹' fundP3, conj (ψ p.2) * eisLow s Y p ∂uhsMeasure =
      ∫ q, T.indicator H q := by
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
  -- step 2: integrability
  have hint : Integrable (T.indicator H) (volume : Measure (ℂ × ℝ)) := by
    rw [integrable_indicator_iff hT]
    have hvolT : volume T ≠ ⊤ := by
      rw [hTdef, Measure.volume_eq_prod, Measure.prod_prod, volume_fundP3, Real.volume_Icc]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
    refine Measure.integrableOn_of_bounded (M := M * cuspC s.re) hvolT hHm.aestronglyMeasurable ?_
    rw [ae_restrict_iff' hT]
    exact Eventually.of_forall hbound
  -- step 3: the inner integrals
  have hslice : ∀ v : ℝ, ∫ z, T.indicator H (z, v) = (Ioi (0 : ℝ)).indicator
      (fun v => ((9 * (Real.sqrt 3 / 2) : ℝ) : ℂ) * eisPhi s *
        (conj (ψ v) * ((v : ℝ) : ℂ) ^ (-1 - s))) v := by
    intro v
    by_cases hv : v ∈ Icc α β
    · have hv0 : 0 < v := lt_of_lt_of_le hα hv.1
      have hYv : Y ≤ v := hYα.trans hv.1
      have h1' : 1 < Y * v := lt_of_lt_of_le h1 (mul_le_mul_of_nonneg_left hv.1 hY.le)
      rw [indicator_of_mem (show v ∈ Ioi (0 : ℝ) from hv0)]
      have e : (fun z => T.indicator H (z, v)) = fundP3.indicator (fun z => H (z, v)) := by
        funext z
        by_cases hz : z ∈ fundP3
        · rw [indicator_of_mem (show (z, v) ∈ T from ⟨hz, hv⟩), indicator_of_mem hz]
        · rw [indicator_of_notMem (show (z, v) ∉ T from fun h => hz h.1), indicator_of_notMem hz]
      rw [e, integral_indicator measurableSet_fundP3]
      simp only [hHdef]
      rw [integral_const_mul, integral_const_mul, integral_fundP3_eisLow hs hY hYv h1',
        ← cpow_neg_one_sub hv0 s]
      ring
    · have e : (fun z => T.indicator H (z, v)) = fun _ => 0 := by
        funext z
        rw [indicator_of_notMem (show (z, v) ∉ T from fun h => hv h.2)]
      rw [e, integral_zero]
      by_cases hv0 : v ∈ Ioi (0 : ℝ)
      · rw [indicator_of_mem hv0, hψ0 v hv, map_zero, zero_mul, mul_zero]
      · rw [indicator_of_notMem hv0]
  -- step 4: Fubini
  rw [hstep1, Measure.volume_eq_prod, integral_prod_symm _ (by rw [← Measure.volume_eq_prod]; exact hint)]
  simp_rw [hslice]
  rw [integral_indicator measurableSet_Ioi, integral_const_mul]

/-- **The finiteness for the unfolding** (round 426's `inner_toLp_pseis`), for `ψ` bounded and vanishing
outside `[α, β]` with `Y > 0`, `α ≥ Y` and `Yα > 1`, and `Re s > 2`. -/
theorem lintegral_rhoT3_eisLow_ne_top {ψ : ℝ → ℂ} {M α β : ℝ} (hM : ∀ v, ‖ψ v‖ ≤ M)
    (hψ0 : ∀ v, v ∉ Icc α β → ψ v = 0) {Y : ℝ} (hY : 0 < Y) (hYα : Y ≤ α) (h1 : 1 < Y * α) {s : ℂ}
    (hs : 2 < s.re) :
    ∫⁻ p, rhoT3 p * ‖conj (ψ p.2) * eisLow s Y p‖ₑ ∂uhsMeasure ≠ ⊤ := by
  have hα1 : 1 ≤ α := (one_lt_of_Y_le hY hYα h1).le
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hT : MeasurableSet (fundP3 ×ˢ Icc α β) := measurableSet_fundP3.prod measurableSet_Icc
  refine ne_top_of_le_ne_top (b := ∫⁻ p, (fundP3 ×ˢ Icc α β).indicator
      (fun _ => ENNReal.ofReal (M * cuspC s.re)) p ∂uhsMeasure) ?_ (lintegral_mono fun p => ?_)
  · rw [lintegral_indicator_const hT]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (uhsMeasure_fundP3_Icc_lt_top hα1).ne
  · by_cases hp : p ∈ fundP3 ×ˢ Icc α β
    · rw [indicator_of_mem hp]
      have hv : α ≤ p.2 := hp.2.1
      have hYv : Y ≤ p.2 := hYα.trans hv
      have h1' : 1 < Y * p.2 := lt_of_lt_of_le h1 (mul_le_mul_of_nonneg_left hv hY.le)
      have hv1 : 1 ≤ p.2 := (one_lt_of_Y_le hY hYv h1').le
      have hE : ‖eisLow s Y p‖ ≤ cuspC s.re := by
        refine (norm_eisLow_le hs hY hYv h1').trans ?_
        have h5 : p.2 ^ (2 - s.re) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hv1 (by linarith)
        have hc := cuspC_nonneg (by linarith : 1 < s.re)
        nlinarith
      calc rhoT3 p * ‖conj (ψ p.2) * eisLow s Y p‖ₑ ≤ 1 * ‖conj (ψ p.2) * eisLow s Y p‖ₑ := by
            gcongr
            exact rhoT3_le_one p
        _ = ENNReal.ofReal ‖conj (ψ p.2) * eisLow s Y p‖ := by rw [one_mul, ofReal_norm]
        _ ≤ ENNReal.ofReal (M * cuspC s.re) := by
            refine ENNReal.ofReal_le_ofReal ?_
            rw [norm_mul, Complex.norm_conj]
            exact mul_le_mul (hM _) hE (norm_nonneg _) hM0
    · rw [indicator_of_notMem hp]
      by_cases h3 : p.1 ∈ fundP3
      · have h4 : p.2 ∉ Icc α β := fun h => hp ⟨h3, h⟩
        rw [hψ0 _ h4, map_zero, zero_mul, enorm_zero, mul_zero]
      · have h0 : rhoT3 p = 0 := by
          unfold rhoT3
          rw [indicator_of_notMem h3]
        rw [h0, zero_mul]

/-- **The pairing with `ũ_s` for `Re s > 2`**: for `R ≥ 0`, `Y > 0`, `ψ` measurable, bounded and vanishing
outside `[α, β]` with `α ≥ Y` and `Yα > 1`, and `Im ĥ(s) ≠ 0`,
`⟨E(ψ), ũ_s⟩ = (9√3/2)·φ(s)·∫_0^∞ conj ψ(v)v^{−1−s} dv`. -/
theorem inner_pseis_uL {R : ℝ} (hR : 0 ≤ R) {Y : ℝ} (hY : 0 < Y) {ψ : ℝ → ℂ} (hψ : Measurable ψ)
    (hψ2 : MemLp (pseis ψ) 2 (muR rhoG)) {M α β : ℝ} (hM : ∀ v, ‖ψ v‖ ≤ M)
    (hψ0 : ∀ v, v ∉ Icc α β → ψ v = 0) (hYα : Y ≤ α) (h1 : 1 < Y * α) {s : ℂ} (hs : 2 < s.re)
    (him : (hhat R s).im ≠ 0) :
    inner ℂ (hψ2.toLp (pseis ψ)) (uL R hR Y hY s) =
      ((9 * (Real.sqrt 3 / 2) : ℝ) : ℂ) * eisPhi s *
        ∫ v in Ioi 0, conj (ψ v) * ((v : ℝ) : ℂ) ^ (-1 - s) := by
  rw [uL_eq_eisLow hR hY hs him, inner_toLp_pseis hψ hψ2 (isAut_eisLow s Y) (measurable_eisLow s Y)
    (memLp_eisLow hs hY.le) (lintegral_rhoT3_eisLow_ne_top hM hψ0 hY hYα h1 hs),
    integral_conj_eisLow hψ hM hψ0 hY hYα h1 hs]

/-- `E(ψ)` is in `L²(ν)` for `ψ` measurable, bounded and vanishing outside `[α, β]` with `α > 0`
(round 424's `memLp_pseis_of_vanish`). -/
theorem memLp_pseis_Icc {ψ : ℝ → ℂ} (hψ : Measurable ψ) {M α β : ℝ} (hM : ∀ v, ‖ψ v‖ ≤ M)
    (hψ0 : ∀ v, v ∉ Icc α β → ψ v = 0) (hα : 0 < α) : MemLp (pseis ψ) 2 (muR rhoG) :=
  memLp_pseis_of_vanish hψ hα ((norm_nonneg _).trans (hM 0))
    (fun v _ hv => hψ0 v fun h => (not_le.2 hv) h.1) (fun v _ => hM v)

/-! ### The Mellin integral of a profile -/

/-- `M_ψ(s) = ∫_0^∞ conj ψ(v)v^{−1−s} dv`. -/
def mellinPsi (ψ : ℝ → ℂ) (s : ℂ) : ℂ := ∫ v in Ioi 0, conj (ψ v) * ((v : ℝ) : ℂ) ^ (-1 - s)

theorem mellinPsi_eq (ψ : ℝ → ℂ) (s : ℂ) :
    mellinPsi ψ s = mellin (fun v => conj (ψ v)) (-s) := by
  unfold mellinPsi mellin
  refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
  rw [smul_eq_mul, mul_comm]
  congr 2
  ring

/-- **`M_ψ` is entire** for `ψ` measurable, bounded and vanishing outside `[α, β]` with `α > 0` (Mathlib's
`mellin_differentiableAt_of_isBigO_rpow`). -/
theorem differentiable_mellinPsi {ψ : ℝ → ℂ} (hψ : Measurable ψ) {M α β : ℝ} (hM : ∀ v, ‖ψ v‖ ≤ M)
    (hψ0 : ∀ v, v ∉ Icc α β → ψ v = 0) (hα : 0 < α) : Differentiable ℂ (mellinPsi ψ) := by
  intro s
  have hf : Measurable fun v => conj (ψ v) := Complex.continuous_conj.measurable.comp hψ
  have hint : Integrable (fun v => conj (ψ v)) := by
    have e : (fun v => conj (ψ v)) = (Icc α β).indicator (fun v => conj (ψ v)) := by
      funext v
      by_cases hv : v ∈ Icc α β
      · rw [indicator_of_mem hv]
      · rw [indicator_of_notMem hv, hψ0 v hv, map_zero]
    rw [e, integrable_indicator_iff measurableSet_Icc]
    refine Measure.integrableOn_of_bounded (M := M)
      (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top) hf.aestronglyMeasurable
      (Eventually.of_forall fun v => ?_)
    rw [Complex.norm_conj]
    exact hM v
  have htop : (fun v => conj (ψ v)) =O[atTop] (fun v : ℝ => v ^ (-(-s.re + 1))) := by
    refine EventuallyEq.trans_isBigO ?_ (Asymptotics.isBigO_zero _ _)
    filter_upwards [eventually_gt_atTop β] with v hv
    rw [hψ0 v (fun h => not_le.2 hv h.2), map_zero]
  have hbot : (fun v => conj (ψ v)) =O[𝓝[>] 0] (fun v : ℝ => v ^ (-(-s.re - 1))) := by
    refine EventuallyEq.trans_isBigO ?_ (Asymptotics.isBigO_zero _ _)
    filter_upwards [Ioo_mem_nhdsGT hα] with v hv
    rw [hψ0 v (fun h => not_le.2 hv.2 h.1), map_zero]
  have hd := mellin_differentiableAt_of_isBigO_rpow (s := -s)
    (hint.locallyIntegrable.locallyIntegrableOn (Ioi 0)) htop (by rw [neg_re]; linarith) hbot
    (by rw [neg_re]; linarith)
  have e : mellinPsi ψ = fun s => mellin (fun v => conj (ψ v)) (-s) := funext (mellinPsi_eq ψ)
  rw [e]
  exact hd.comp s differentiableAt_id.neg

/-! ### The identity theorem -/

/-- The domain `{Re s > 1, 0 < Im s < π/r}`, where `Im ĥ(s) > 0` (round 418's `im_hhat_pos`). -/
def domU (r : ℝ) : Set ℂ := {s | 1 < s.re} ∩ ({s | 0 < s.im} ∩ {s | s.im < Real.pi / r})

theorem isOpen_domU (r : ℝ) : IsOpen (domU r) :=
  (isOpen_lt continuous_const continuous_re).inter
    ((isOpen_lt continuous_const continuous_im).inter (isOpen_lt continuous_im continuous_const))

theorem convex_domU (r : ℝ) : Convex ℝ (domU r) :=
  (convex_halfSpace_re_gt 1).inter ((convex_halfSpace_im_gt 0).inter (convex_halfSpace_im_lt _))

/-- **The pairing of θ with a pseudo-Eisenstein series**: for `r > 0`, `Y > 0`, and `ψ` measurable, bounded
and vanishing outside `[α, β]` with `α ≥ Y` and `Yα > 1`, `⟨E(ψ), θ⟩ = (9√3/2)·Res φ·M_ψ(4/3)`, with
`Res φ = phiG(4/3)/3` (round 417). -/
theorem inner_pseis_thetaL {r : ℝ} (hr : 0 < r) {Y : ℝ} (hY : 0 < Y) {ψ : ℝ → ℂ} (hψ : Measurable ψ)
    (hψ2 : MemLp (pseis ψ) 2 (muR rhoG)) {M α β : ℝ} (hM : ∀ v, ‖ψ v‖ ≤ M)
    (hψ0 : ∀ v, v ∉ Icc α β → ψ v = 0) (hYα : Y ≤ α) (h1 : 1 < Y * α) :
    inner ℂ (hψ2.toLp (pseis ψ)) (thetaL r Y hY) =
      ((9 * (Real.sqrt 3 / 2) : ℝ) : ℂ) * (phiG (4 / 3) / 3) * mellinPsi ψ (4 / 3) := by
  set R := 2 * Real.cosh r - 2 with hRdef
  set y := hψ2.toLp (pseis ψ) with hy
  set c9 : ℂ := ((9 * (Real.sqrt 3 / 2) : ℝ) : ℂ) with hc9
  have hα : 0 < α := lt_of_lt_of_le hY hYα
  set F : ℂ → ℂ := fun s => inner ℂ y (uL R (cosh_sub_nonneg r) Y hY s) with hF
  set G : ℂ → ℂ := fun s => c9 * phiC s * mellinPsi ψ s with hG
  have hMd := differentiable_mellinPsi hψ hM hψ0 hα
  have him : ∀ s ∈ domU r, (hhat R s).im ≠ 0 := fun s hs =>
    (im_hhat_pos hr hs.1 hs.2.1 ((lt_div_iff₀ hr).1 hs.2.2)).ne'
  have hFd : DifferentiableOn ℂ F (domU r) := fun s hs =>
    (differentiableAt_inner_uL hr.le hY y (him s hs)).differentiableWithinAt
  have hGd : DifferentiableOn ℂ G (domU r) := fun s hs => by
    have h43 : s ≠ 4 / 3 := fun h => by
      have h2 := hs.2.1
      rw [h] at h2
      norm_num at h2
    exact (((differentiableAt_phiC hs.1 h43).const_mul c9).mul (hMd s)).differentiableWithinAt
  -- agreement where `Re s > 2`
  obtain ⟨x, hxdef⟩ : ∃ x : ℝ, x = Real.pi / (2 * r) := ⟨_, rfl⟩
  have hx0 : 0 < x := by rw [hxdef]; positivity
  have hxr : x < Real.pi / r := by
    rw [hxdef, div_lt_div_iff₀ (by positivity) hr]
    nlinarith [Real.pi_pos]
  set z0 : ℂ := 3 + I * (x : ℂ) with hz0def
  have hz0re : z0.re = 3 := by simp [z0]
  have hz0im : z0.im = x := by simp [z0]
  have hz0 : z0 ∈ domU r := by
    refine ⟨?_, ?_, ?_⟩
    · show 1 < z0.re
      rw [hz0re]
      norm_num
    · show 0 < z0.im
      rw [hz0im]
      exact hx0
    · show z0.im < Real.pi / r
      rw [hz0im]
      exact hxr
  have hfg : F =ᶠ[𝓝 z0] G := by
    have hO : IsOpen (domU r ∩ {s | 2 < s.re}) :=
      (isOpen_domU r).inter (isOpen_lt continuous_const continuous_re)
    have hmem : z0 ∈ domU r ∩ {s | 2 < s.re} := ⟨hz0, by show 2 < z0.re; rw [hz0re]; norm_num⟩
    filter_upwards [hO.mem_nhds hmem] with s hs
    simp only [hF, hG]
    rw [inner_pseis_uL (cosh_sub_nonneg r) hY hψ hψ2 hM hψ0 hYα h1 hs.2 (him s hs.1),
      eisPhi_eq_phiC hs.2]
    rfl
  have heq : EqOn F G (domU r) :=
    (hFd.analyticOnNhd (isOpen_domU r)).eqOn_of_preconnected_of_eventuallyEq
      (hGd.analyticOnNhd (isOpen_domU r)) (convex_domU r).isPreconnected hz0 hfg
  -- the curve `s = 4/3 + iε`
  set γ : ℝ → ℂ := fun ε => ((4 / 3 : ℝ) : ℂ) + I * ε with hγdef
  have hγU : ∀ᶠ ε in 𝓝[>] (0 : ℝ), γ ε ∈ domU r := by
    filter_upwards [Ioo_mem_nhdsGT (div_pos Real.pi_pos hr)] with ε hε
    refine ⟨?_, ?_, ?_⟩
    · show 1 < (γ ε).re
      simp [γ]
      norm_num
    · show 0 < (γ ε).im
      simp [γ, hε.1]
    · show (γ ε).im < Real.pi / r
      simp [γ, hε.2]
  have hL : Tendsto (fun ε : ℝ => (I * ε) * F (γ ε)) (𝓝[>] 0) (𝓝 (inner ℂ y (thetaL r Y hY))) := by
    have h := ((innerSL ℂ y).continuous.tendsto _).comp (tendsto_uL_thetaL hr hY)
    refine h.congr fun ε => ?_
    simp only [Function.comp, hF, hγdef, innerSL_apply_apply, inner_smul_right]
    rfl
  have hγ : Tendsto γ (𝓝[>] 0) (𝓝[≠] (4 / 3 : ℂ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have h0 : γ 0 = 4 / 3 := by
        simp only [γ, ofReal_zero, mul_zero, add_zero]
        push_cast
        ring
      have hc : Continuous γ := by fun_prop
      have := hc.tendsto 0
      rw [h0] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      intro h
      have := congrArg Complex.im h
      simp [γ] at this
      exact (ne_of_gt (show (0 : ℝ) < ε from hε)) this
  have hRt : Tendsto (fun ε : ℝ => (I * ε) * G (γ ε)) (𝓝[>] 0)
      (𝓝 (c9 * (phiG (4 / 3) / 3) * mellinPsi ψ (4 / 3))) := by
    have h1' := tendsto_phiC_residue.comp hγ
    have h2 : Tendsto (fun ε => mellinPsi ψ (γ ε)) (𝓝[>] 0) (𝓝 (mellinPsi ψ (4 / 3))) :=
      (hMd (4 / 3)).continuousAt.tendsto.comp (hγ.mono_right nhdsWithin_le_nhds)
    have h3 := (h1'.const_mul c9).mul h2
    refine h3.congr fun ε => ?_
    simp only [Function.comp, hG]
    have e : γ ε - 4 / 3 = I * ε := by
      simp only [γ]
      push_cast
      ring
    rw [e]
    ring
  have hEq : (fun ε : ℝ => (I * ε) * F (γ ε)) =ᶠ[𝓝[>] (0 : ℝ)] fun ε => (I * ε) * G (γ ε) := by
    filter_upwards [hγU] with ε hε
    rw [heq hε]
  exact tendsto_nhds_unique (hL.congr' hEq) hRt

/-! ### θ ≠ 0 -/

/-- `M_ψ(4/3) > 0` for `ψ = 1_{[α, β]}` with `0 < α < β`. -/
theorem mellinPsi_indicator_ne_zero {α β : ℝ} (hα : 0 < α) (hαβ : α < β) :
    mellinPsi ((Icc α β).indicator fun _ => (1 : ℂ)) (4 / 3) ≠ 0 := by
  have e : mellinPsi ((Icc α β).indicator fun _ => (1 : ℂ)) (4 / 3) =
      ((∫ v in α..β, v ^ (-(7 / 3) : ℝ) : ℝ) : ℂ) := by
    unfold mellinPsi
    have e1 : ∀ v ∈ Ioi (0 : ℝ), conj ((Icc α β).indicator (fun _ => (1 : ℂ)) v) *
        ((v : ℝ) : ℂ) ^ (-1 - 4 / 3 : ℂ) =
          (Icc α β).indicator (fun v => (((v ^ (-(7 / 3) : ℝ) : ℝ)) : ℂ)) v := by
      intro v hv
      by_cases h : v ∈ Icc α β
      · rw [indicator_of_mem h, indicator_of_mem h, map_one, one_mul,
          ofReal_cpow (le_of_lt hv)]
        congr 1
        push_cast
        ring
      · rw [indicator_of_notMem h, indicator_of_notMem h, map_zero, zero_mul]
    have hsub : Icc α β ⊆ Ioi (0 : ℝ) := fun v hv => lt_of_lt_of_le hα hv.1
    rw [setIntegral_congr_fun measurableSet_Ioi e1, setIntegral_indicator measurableSet_Icc,
      inter_eq_right.2 hsub, integral_complex_ofReal,
      integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hαβ.le]
  rw [e, Ne, ofReal_eq_zero]
  refine ne_of_gt (intervalIntegral.intervalIntegral_pos_of_pos_on ?_ (fun v hv => ?_) hαβ)
  · refine intervalIntegral.intervalIntegrable_rpow (Or.inr fun h => ?_)
    rw [uIcc_of_le hαβ.le] at h
    exact absurd h.1 (not_le.2 hα)
  · exact Real.rpow_pos_of_pos (lt_trans hα hv.1) _

/-- **θ ≠ 0**, for `r > 0` and `Y > 0`: its pairing with the pseudo-Eisenstein series of `1_{[α, α + 1]}`,
`α = Y + 1/Y`, is `(9√3/2)·Res φ·∫_α^{α+1} v^{−7/3} dv ≠ 0` (round 417's `phiRes_ne_zero`). -/
theorem thetaL_ne_zero {r : ℝ} (hr : 0 < r) {Y : ℝ} (hY : 0 < Y) : thetaL r Y hY ≠ 0 := by
  set α : ℝ := Y + 1 / Y with hαdef
  set ψ : ℝ → ℂ := (Icc α (α + 1)).indicator fun _ => (1 : ℂ) with hψdef
  have hψ : Measurable ψ := measurable_const.indicator measurableSet_Icc
  have hM : ∀ v, ‖ψ v‖ ≤ 1 := fun v => by
    by_cases hv : v ∈ Icc α (α + 1)
    · rw [hψdef, indicator_of_mem hv, norm_one]
    · rw [hψdef, indicator_of_notMem hv, norm_zero]
      exact zero_le_one
  have hψ0 : ∀ v, v ∉ Icc α (α + 1) → ψ v = 0 := fun v hv => indicator_of_notMem hv _
  have hYα : Y ≤ α := by
    have : 0 < 1 / Y := by positivity
    linarith
  have h1 : 1 < Y * α := by
    rw [hαdef, mul_add, mul_one_div_cancel hY.ne']
    nlinarith
  have hα : 0 < α := lt_of_lt_of_le hY hYα
  have hψ2 := memLp_pseis_Icc hψ hM hψ0 hα
  have hpair := inner_pseis_thetaL hr hY hψ hψ2 hM hψ0 hYα h1
  intro h0
  rw [h0, inner_zero_right] at hpair
  have hc9 : (((9 * (Real.sqrt 3 / 2) : ℝ) : ℂ)) ≠ 0 := by
    have : (0 : ℝ) < 9 * (Real.sqrt 3 / 2) := by positivity
    exact_mod_cast this.ne'
  exact mul_ne_zero (mul_ne_zero hc9 phiRes_ne_zero)
    (mellinPsi_indicator_ne_zero hα (by linarith)) hpair.symm

end Eis

end

#print axioms Eis.height_le_inv
#print axioms Eis.eisHigh_eq
#print axioms Eis.eisLow_eq_sub
#print axioms Eis.one_lt_of_Y_le
#print axioms Eis.norm_eisLow_le
#print axioms Eis.integral_fundP3_eisLow
#print axioms Eis.cpow_neg_one_sub
#print axioms Eis.uhsMeasure_fundP3_Icc_lt_top
#print axioms Eis.integral_conj_eisLow
#print axioms Eis.lintegral_rhoT3_eisLow_ne_top
#print axioms Eis.inner_pseis_uL
#print axioms Eis.memLp_pseis_Icc
#print axioms Eis.mellinPsi_eq
#print axioms Eis.differentiable_mellinPsi
#print axioms Eis.isOpen_domU
#print axioms Eis.convex_domU
#print axioms Eis.inner_pseis_thetaL
#print axioms Eis.mellinPsi_indicator_ne_zero
#print axioms Eis.thetaL_ne_zero
