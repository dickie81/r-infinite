import KubotaThetaCoef

/-! # The constant term of θ (round 433)

S5f-10 of round 360's plan, part 16 (S5f-10f, sixth part). Round 432's next step planned the constant term of
θ's representative `θ̃` (round 425's `thetaF`) for all `v > 0`. This round proves it, for `r > 0`, `Y > 0`,
and `ψ` measurable and bounded, vanishing outside `[α, β]` with `0 < α ≤ β`:

* **The pairing for `Re s > 2`** (**`inner_pseis_uL_band`**, with `setLIntegral_lt_top_of_bdd` and
  `lintegral_rhoT3_ps_ne_top`): for `Im ĥ(s) ≠ 0`,
  `⟨E(ψ), ũ_s⟩ = (9√3/2)·(M_ψ(2 − s) + φ(s)M_ψ(s)) − ⟨E(ψ), E(1[Y ≤ v ≤ H]v^s)⟩` with `H = Y + β + 1/α`, by
  round 430's band series and round 389's `constTerm_eis1`.
* **The residue** (**`inner_pseis_thetaL_gen`**): `⟨E(ψ), θ⟩ = (9√3/2)·Res φ·M_ψ(4/3)` with
  `Res φ = phiG(4/3)/3`, by the identity theorem and the limit as in round 427, without round 427's condition
  `α ≥ Y`, `Yα > 1`.
* **The constant term** (**`inner_pseis_thetaL_unfold`** and **`const_thetaF_ae`**, with `integrableOn_thetaF`
  and `ae_eq_of_setIntegral_Icc`): `⟨E(ψ), θ⟩ = ∫_0^∞ v^{−3}·conj ψ(v)·∫_{3P} θ̃(z, v) dz dv` (round 426's
  `inner_toLp_pseis`, with round 432's local integrability), so `∫_{3P} θ̃(z, v) dz = (9√3/2)·Res φ·v^{2/3}`
  for almost every `v > 0`.
-/

open MeasureTheory Set Filter NumberField Complex Ideal Asymptotics
open scoped ENNReal Topology MatrixGroups ComplexConjugate

noncomputable section

namespace Eis

/-! ### The pairing of `E(ψ)` with `ũ_s` for every profile -/

/-- `∫_{3P×[α,β]} |G| dz dv/v³ < ∞` for `G` bounded on `3P × [α, β]`, `α > 0`. -/
theorem setLIntegral_lt_top_of_bdd {G : ℂ × ℝ → ℂ} {α β B : ℝ} (hα : 0 < α)
    (hB : ∀ p ∈ fundP3 ×ˢ Icc α β, ‖G p‖ ≤ B) :
    ∫⁻ p in fundP3 ×ˢ Icc α β, ‖G p‖ₑ ∂uhsMeasure < ⊤ := by
  calc ∫⁻ p in fundP3 ×ˢ Icc α β, ‖G p‖ₑ ∂uhsMeasure
      ≤ ∫⁻ _ in fundP3 ×ˢ Icc α β, ENNReal.ofReal B ∂uhsMeasure :=
        setLIntegral_mono measurable_const fun p hp => by
          rw [← ofReal_norm]
          exact ENNReal.ofReal_le_ofReal (hB p hp)
    _ = ENNReal.ofReal B * uhsMeasure (fundP3 ×ˢ Icc α β) := setLIntegral_const _ _
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (uhsMeasure_fundP3_Icc_lt_top_of_pos hα)

/-- **The finiteness for the unfolding of `E(ψ)`**, for `ψ` vanishing outside `[α, β]` and
`∫_{3P×[α,β]} |G| dz dv/v³ < ∞`. -/
theorem lintegral_rhoT3_ps_ne_top {ψ : ℝ → ℂ} {M α β : ℝ} (hM : ∀ v, ‖ψ v‖ ≤ M)
    (hψ0 : ∀ v, v ∉ Icc α β → ψ v = 0) {G : ℂ × ℝ → ℂ} (hGm : Measurable G)
    (hG : ∫⁻ p in fundP3 ×ˢ Icc α β, ‖G p‖ₑ ∂uhsMeasure < ⊤) :
    ∫⁻ p, rhoT3 p * ‖conj (ψ p.2) * G p‖ₑ ∂uhsMeasure ≠ ⊤ := by
  have hT : MeasurableSet (fundP3 ×ˢ Icc α β) := measurableSet_fundP3.prod measurableSet_Icc
  refine ne_top_of_le_ne_top
    (b := ∫⁻ p in fundP3 ×ˢ Icc α β, ENNReal.ofReal M * ‖G p‖ₑ ∂uhsMeasure) ?_ ?_
  · rw [lintegral_const_mul _ hGm.enorm]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hG.ne
  · rw [← lintegral_indicator hT]
    refine lintegral_mono fun p => ?_
    by_cases hp : p ∈ fundP3 ×ˢ Icc α β
    · rw [indicator_of_mem hp]
      calc rhoT3 p * ‖conj (ψ p.2) * G p‖ₑ ≤ 1 * ‖conj (ψ p.2) * G p‖ₑ := by
            gcongr
            exact rhoT3_le_one p
        _ ≤ ENNReal.ofReal M * ‖G p‖ₑ := by
            rw [one_mul, enorm_mul, ← ofReal_norm (conj _), Complex.norm_conj]
            gcongr
            exact hM _
    · by_cases h3 : p.1 ∈ fundP3
      · have h4 : p.2 ∉ Icc α β := fun h => hp ⟨h3, h⟩
        rw [hψ0 _ h4, map_zero, zero_mul, enorm_zero, mul_zero]
        exact zero_le
      · have h0 : rhoT3 p = 0 := by
          unfold rhoT3
          rw [indicator_of_notMem h3]
        rw [h0, zero_mul]
        exact zero_le

/-- **The pairing of `E(ψ)` with `ũ_s` for `Re s > 2`**: for `R ≥ 0`, `Y > 0`, `ψ` measurable and bounded,
vanishing outside `[α, β]` with `0 < α ≤ β`, and `Im ĥ(s) ≠ 0`,
`⟨E(ψ), ũ_s⟩ = (9√3/2)·(M_ψ(2 − s) + φ(s)M_ψ(s)) − ⟨E(ψ), E(1[Y ≤ v ≤ H]v^s)⟩` with `H = Y + β + 1/α`. -/
theorem inner_pseis_uL_band {R : ℝ} (hR : 0 ≤ R) {Y : ℝ} (hY : 0 < Y) {ψ : ℝ → ℂ} (hψ : Measurable ψ)
    (hψ2 : MemLp (pseis ψ) 2 (muR rhoG)) {M α β : ℝ} (hM : ∀ v, ‖ψ v‖ ≤ M)
    (hψ0 : ∀ v, v ∉ Icc α β → ψ v = 0) (hα : 0 < α) (hαβ : α ≤ β) {s : ℂ} (hs : 2 < s.re)
    (him : (hhat R s).im ≠ 0) :
    inner ℂ (hψ2.toLp (pseis ψ)) (uL R hR Y hY s) =
      ((9 * (Real.sqrt 3 / 2) : ℝ) : ℂ) * (mellinPsi ψ (2 - s) + eisPhi s * mellinPsi ψ s) -
        inner ℂ (hψ2.toLp (pseis ψ)) (bandL hY (le_band hα hαβ) s) := by
  set H := Y + β + 1 / α
  have hσ : 2 < s.re := hs
  set Bd := hBd s.re α β
  have hbL : ∀ v, 0 < v → ‖lowF s Y v‖ ≤ v ^ s.re := fun v hv => by
    have := norm_lowF_le s Y hv
    rwa [one_mul] at this
  have hbB : ∀ v, 0 < v → ‖bandF s Y H v‖ ≤ v ^ s.re := fun v hv => by
    unfold bandF
    split_ifs
    · rw [Complex.norm_cpow_eq_rpow_re_of_pos hv]
    · rw [norm_zero]
      exact Real.rpow_nonneg hv.le _
  have hbE : ∀ v, 0 < v → ‖((v : ℝ) : ℂ) ^ s‖ ≤ v ^ s.re := fun v hv => by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hv]
  have bL : ∀ p ∈ fundP3 ×ˢ Icc α β, ‖eisLow s Y p‖ ≤ Bd :=
    fun p hp => norm_pseis_le_hBd hσ hbL hα hp.1 hp.2.1 hp.2.2
  have bB : ∀ p ∈ fundP3 ×ˢ Icc α β, ‖pseis (bandF s Y H) p‖ ≤ Bd :=
    fun p hp => norm_pseis_le_hBd hσ hbB hα hp.1 hp.2.1 hp.2.2
  have bE : ∀ p ∈ fundP3 ×ˢ Icc α β, ‖eis1 s p‖ ≤ Bd :=
    fun p hp => by rw [eis1_eq_pseis]; exact norm_pseis_le_hBd hσ hbE hα hp.1 hp.2.1 hp.2.2
  have hE1m : Measurable (eis1 s) := by
    rw [eis1_eq_pseis]
    exact measurable_pseis (Complex.measurable_ofReal.pow_const s)
  have hBm : Measurable (pseis (bandF s Y H)) := measurable_pseis (measurable_bandF s Y H)
  rw [uL_eq_eisLow hR hY hs him,
    inner_toLp_pseis hψ hψ2 (isAut_eisLow s Y) (measurable_eisLow s Y) (memLp_eisLow hs hY.le)
      (lintegral_rhoT3_ps_ne_top hM hψ0 (measurable_eisLow s Y) (setLIntegral_lt_top_of_bdd hα bL)),
    bandL, inner_toLp_pseis hψ hψ2 (isAut_pseis _) hBm (memLp_pseis_bandF s hY (le_band hα hαβ))
      (lintegral_rhoT3_ps_ne_top hM hψ0 hBm (setLIntegral_lt_top_of_bdd hα bB))]
  have h1 : ∫ p in Prod.fst ⁻¹' fundP3, conj (ψ p.2) * eisLow s Y p ∂uhsMeasure =
      ∫ p in Prod.fst ⁻¹' fundP3,
        (conj (ψ p.2) * eis1 s p - conj (ψ p.2) * pseis (bandF s Y H) p) ∂uhsMeasure := by
    refine setIntegral_congr_fun (measurableSet_fundP3.preimage measurable_fst) fun p _ => ?_
    by_cases hv : p.2 ∈ Icc α β
    · rw [eisLow_eq_band hs hY hα hv.1 hv.2]
      ring
    · simp [hψ0 _ hv]
  rw [h1, integral_sub (integrableOn_fundP3_of_bdd hψ hM hψ0 hα hE1m (fun p h1 h2 => bE p ⟨h1, h2⟩))
      (integrableOn_fundP3_of_bdd hψ hM hψ0 hα hBm (fun p h1 h2 => bB p ⟨h1, h2⟩)),
    integral_fundP3_conj_mul hψ hM hψ0 hα hE1m (fun p h1 h2 => bE p ⟨h1, h2⟩)]
  congr 1
  have hc9 : ((9 * (Real.sqrt 3 / 2) : ℝ) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < 9 * (Real.sqrt 3 / 2) := by positivity
    exact_mod_cast this.ne'
  have e : ∫ v in Ioi 0, ((v ^ (-3 : ℤ) : ℝ) : ℂ) * conj (ψ v) * ∫ z in fundP3, eis1 s (z, v) =
      ∫ v in Ioi 0, (((9 * (Real.sqrt 3 / 2) : ℝ) : ℂ) * (conj (ψ v) * ((v : ℝ) : ℂ) ^ (-1 - (2 - s))) +
        ((9 * (Real.sqrt 3 / 2) : ℝ) : ℂ) * eisPhi s * (conj (ψ v) * ((v : ℝ) : ℂ) ^ (-1 - s))) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun v hv => ?_
    have hv' : (0 : ℝ) < v := hv
    have hc := constTerm_eis1 hs hv'
    have hI : ∫ z in fundP3, eis1 s (z, v) = ((9 * (Real.sqrt 3 / 2) : ℝ) : ℂ) *
        (((v : ℝ) : ℂ) ^ s + eisPhi s * ((v : ℝ) : ℂ) ^ (2 - s)) := by
      rw [← hc, ← mul_assoc, mul_inv_cancel₀ hc9, one_mul]
    rw [hI]
    have e1 : ((v ^ (-3 : ℤ) : ℝ) : ℂ) * ((v : ℝ) : ℂ) ^ s = ((v : ℝ) : ℂ) ^ (-1 - (2 - s)) := by
      have := cpow_neg_one_sub hv' (2 - s)
      rwa [sub_sub_cancel] at this
    have e2 := cpow_neg_one_sub hv' s
    rw [← e1, ← e2]
    ring
  rw [e]
  have hc1 : ContinuousOn (fun v : ℝ => ((v : ℝ) : ℂ) ^ (-1 - (2 - s))) (Ioi 0) := fun v hv =>
    (continuousAt_ofReal_cpow_const v _ (Or.inr (show (0 : ℝ) < v from hv).ne')).continuousWithinAt
  have hc2 : ContinuousOn (fun v : ℝ => ((v : ℝ) : ℂ) ^ (-1 - s)) (Ioi 0) := fun v hv =>
    (continuousAt_ofReal_cpow_const v _ (Or.inr (show (0 : ℝ) < v from hv).ne')).continuousWithinAt
  rw [integral_add ((integrableOn_Ioi_conj_mul hψ hM hψ0 hα hc1).const_mul _)
      ((integrableOn_Ioi_conj_mul hψ hM hψ0 hα hc2).const_mul _), integral_const_mul,
    integral_const_mul]
  unfold mellinPsi
  ring

/-- **The pairing of θ with a pseudo-Eisenstein series, for every profile**: for `r > 0`, `Y > 0`, and `ψ`
measurable and bounded, vanishing outside `[α, β]` with `0 < α ≤ β`, `⟨E(ψ), θ⟩ = (9√3/2)·Res φ·M_ψ(4/3)`
with `Res φ = phiG(4/3)/3` (round 427's `inner_pseis_thetaL` without its condition `α ≥ Y`, `Yα > 1`). -/
theorem inner_pseis_thetaL_gen {r : ℝ} (hr : 0 < r) {Y : ℝ} (hY : 0 < Y) {ψ : ℝ → ℂ}
    (hψ : Measurable ψ) (hψ2 : MemLp (pseis ψ) 2 (muR rhoG)) {M α β : ℝ} (hM : ∀ v, ‖ψ v‖ ≤ M)
    (hψ0 : ∀ v, v ∉ Icc α β → ψ v = 0) (hα : 0 < α) (hαβ : α ≤ β) :
    inner ℂ (hψ2.toLp (pseis ψ)) (thetaL r Y hY) =
      ((9 * (Real.sqrt 3 / 2) : ℝ) : ℂ) * (phiG (4 / 3) / 3) * mellinPsi ψ (4 / 3) := by
  set R := 2 * Real.cosh r - 2 with hRdef
  set y := hψ2.toLp (pseis ψ) with hy
  set c9 : ℂ := ((9 * (Real.sqrt 3 / 2) : ℝ) : ℂ) with hc9
  have hMd := differentiable_mellinPsi hψ hM hψ0 hα
  set F : ℂ → ℂ := fun s => inner ℂ y (uL R (cosh_sub_nonneg r) Y hY s) +
    inner ℂ y (bandL hY (le_band hα hαβ) s) - c9 * mellinPsi ψ (2 - s) with hF
  set G : ℂ → ℂ := fun s => c9 * phiC s * mellinPsi ψ s with hG
  have him : ∀ s ∈ domU r, (hhat R s).im ≠ 0 := fun s hs =>
    (im_hhat_pos hr hs.1 hs.2.1 ((lt_div_iff₀ hr).1 hs.2.2)).ne'
  have hc : ∀ s : ℂ, DifferentiableAt ℂ (fun s : ℂ => 2 - s) s := fun s =>
    (differentiableAt_const 2).sub differentiableAt_id
  have hFd : DifferentiableOn ℂ F (domU r) := fun s hs => by
    have h1 := differentiableAt_inner_uL hr.le hY y (him s hs)
    have h2 := differentiable_inner_bandL y hY (le_band hα hαβ) s
    have h3 : DifferentiableAt ℂ (fun s => mellinPsi ψ (2 - s)) s :=
      DifferentiableAt.comp (g := mellinPsi ψ) s (hMd (2 - s)) (hc s)
    exact ((h1.add h2).sub (h3.const_mul c9)).differentiableWithinAt
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
    rw [inner_pseis_uL_band (cosh_sub_nonneg r) hY hψ hψ2 hM hψ0 hα hαβ hs.2 (him s hs.1),
      eisPhi_eq_phiC hs.2]
    ring
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
  have hγc : Tendsto γ (𝓝[>] 0) (𝓝 ((4 / 3 : ℝ) : ℂ)) := by
    have hcont : Continuous γ := by fun_prop
    have := hcont.tendsto 0
    have h0 : γ 0 = ((4 / 3 : ℝ) : ℂ) := by simp [γ]
    rw [h0] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hI : Tendsto (fun ε : ℝ => I * (ε : ℂ)) (𝓝[>] 0) (𝓝 0) := by
    have hcont : Continuous fun ε : ℝ => I * (ε : ℂ) := by fun_prop
    have := hcont.tendsto 0
    simp only [ofReal_zero, mul_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hL0 : Tendsto (fun ε : ℝ => (I * ε) *
      inner ℂ y (uL R (cosh_sub_nonneg r) Y hY (γ ε))) (𝓝[>] 0) (𝓝 (inner ℂ y (thetaL r Y hY))) := by
    have h := ((innerSL ℂ y).continuous.tendsto _).comp (tendsto_uL_thetaL hr hY)
    refine h.congr fun ε => ?_
    simp only [Function.comp, hγdef, innerSL_apply_apply, inner_smul_right]
    rfl
  have hB : Tendsto (fun ε : ℝ => inner ℂ y (bandL hY (le_band hα hαβ) (γ ε)) - c9 * mellinPsi ψ (2 - γ ε))
      (𝓝[>] 0) (𝓝 (inner ℂ y (bandL hY (le_band hα hαβ) ((4 / 3 : ℝ) : ℂ)) -
        c9 * mellinPsi ψ (2 - ((4 / 3 : ℝ) : ℂ)))) := by
    refine ((differentiable_inner_bandL y hY (le_band hα hαβ) _).continuousAt.tendsto.comp hγc).sub
      (tendsto_const_nhds.mul ((hMd _).continuousAt.tendsto.comp (tendsto_const_nhds.sub hγc)))
  have hL : Tendsto (fun ε : ℝ => (I * ε) * F (γ ε)) (𝓝[>] 0) (𝓝 (inner ℂ y (thetaL r Y hY))) := by
    have h := hL0.add (hI.mul hB)
    rw [zero_mul, add_zero] at h
    refine h.congr fun ε => ?_
    simp only [hF]
    ring
  have hγ : Tendsto γ (𝓝[>] 0) (𝓝[≠] (4 / 3 : ℂ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have e : ((4 / 3 : ℝ) : ℂ) = 4 / 3 := by push_cast; ring
      rw [← e]
      exact hγc
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

/-! ### The constant term of θ -/

/-- `θ̃` is integrable on `3P × [α, β]` against `dz dv`, for `α > 0`. -/
theorem integrableOn_thetaF {r : ℝ} (hr : 0 < r) {Y : ℝ} (hY : 0 < Y) {α : ℝ} (hα : 0 < α) (β : ℝ) :
    IntegrableOn (thetaF r Y hY) (fundP3 ×ˢ Icc α β) := by
  have hT : MeasurableSet (fundP3 ×ˢ Icc α β) := measurableSet_fundP3.prod measurableSet_Icc
  refine ⟨(measurable_thetaF r Y hY).aestronglyMeasurable, ?_⟩
  show ∫⁻ p in fundP3 ×ˢ Icc α β, ‖thetaF r Y hY p‖ₑ < ⊤
  refine (setLIntegral_volume_le (measurable_thetaF r Y hY).enorm hT hα
    (fun p hp => ⟨hp.2.1, hp.2.2⟩)).trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_)
  exact (lintegral_mono_set (fun p hp => (⟨norm_le_six_of_mem_fundP3 hp.1, hp.2.1, hp.2.2⟩ :
    p ∈ boxZ 6 α β))).trans_lt (lintegral_boxZ_thetaF_lt_top hr hY 6 hα β)

/-- **The pairing of θ with `E(ψ)`, unfolded**: for `ψ` measurable and bounded, vanishing outside `[α, β]`
with `α > 0`, `⟨E(ψ), θ⟩ = ∫_0^∞ v^{−3}·conj ψ(v)·∫_{3P} θ̃(z, v) dz dv`. -/
theorem inner_pseis_thetaL_unfold {r : ℝ} (hr : 0 < r) {Y : ℝ} (hY : 0 < Y) {ψ : ℝ → ℂ}
    (hψ : Measurable ψ) (hψ2 : MemLp (pseis ψ) 2 (muR rhoG)) {M α β : ℝ} (hM : ∀ v, ‖ψ v‖ ≤ M)
    (hψ0 : ∀ v, v ∉ Icc α β → ψ v = 0) (hα : 0 < α) :
    inner ℂ (hψ2.toLp (pseis ψ)) (thetaL r Y hY) =
      ∫ v in Ioi 0, ((v ^ (-3 : ℤ) : ℝ) : ℂ) * conj (ψ v) * ∫ z in fundP3, thetaF r Y hY (z, v) := by
  have hθ : thetaL r Y hY = (memLp_thetaF hr hY).toLp (thetaF r Y hY) :=
    Lp.ext ((thetaL_ae_eq_thetaF hr hY).trans (memLp_thetaF hr hY).coeFn_toLp.symm)
  have hfin := lintegral_rhoT3_ps_ne_top hM hψ0 (measurable_thetaF r Y hY)
    ((lintegral_mono_set (fun p hp => (⟨norm_le_six_of_mem_fundP3 hp.1, hp.2.1, hp.2.2⟩ :
      p ∈ boxZ 6 α β))).trans_lt (lintegral_boxZ_thetaF_lt_top hr hY 6 hα β))
  rw [hθ, inner_toLp_pseis hψ hψ2 (isAut_thetaF r Y hY) (measurable_thetaF r Y hY) (memLp_thetaF hr hY)
    hfin, integral_fundP3_conj_mul_of_int hψ hM hψ0 hα (measurable_thetaF r Y hY)
      (integrableOn_thetaF hr hY hα β)]

/-- **Equality almost everywhere from the integrals over subsets of `[1/(n + 1), n + 1]`**: functions
integrable on each of these intervals, with equal integrals over every measurable subset of them, agree
almost everywhere on `(0, ∞)`. -/
theorem ae_eq_of_setIntegral_Icc {f g : ℝ → ℂ}
    (hf : ∀ n : ℕ, IntegrableOn f (Icc (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1)))
    (hg : ∀ n : ℕ, IntegrableOn g (Icc (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1)))
    (h : ∀ n : ℕ, ∀ S : Set ℝ, MeasurableSet S → S ⊆ Icc (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1) →
      ∫ v in S, f v = ∫ v in S, g v) :
    ∀ᵐ v ∂(volume.restrict (Ioi (0 : ℝ))), f v = g v := by
  rw [Ioi_zero_eq_iUnion_Icc, ae_restrict_iUnion_iff]
  intro n
  have hfg : IntegrableOn (fun v => f v - g v) (Icc (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1)) :=
    (hf n).sub (hg n)
  have h0 := hfg.ae_eq_zero_of_forall_setIntegral_eq_zero fun s hs _ => by
    rw [Measure.restrict_restrict hs, integral_sub ((hf n).mono_set inter_subset_right)
      ((hg n).mono_set inter_subset_right), h n _ (hs.inter measurableSet_Icc) inter_subset_right,
      sub_self]
  filter_upwards [h0] with v hv
  exact sub_eq_zero.1 hv

/-- **The constant term of θ**: for `r > 0` and `Y > 0`, `∫_{3P} θ̃(z, v) dz = (9√3/2)·Res φ·v^{2/3}` for
almost every `v > 0`, with `Res φ = phiG(4/3)/3` (round 417). -/
theorem const_thetaF_ae {r : ℝ} (hr : 0 < r) {Y : ℝ} (hY : 0 < Y) :
    ∀ᵐ v ∂(volume.restrict (Ioi (0 : ℝ))), ∫ z in fundP3, thetaF r Y hY (z, v) =
      ((9 * (Real.sqrt 3 / 2) : ℝ) : ℂ) * (phiG (4 / 3) / 3) * ((v ^ (2 / 3 : ℝ) : ℝ) : ℂ) := by
  set C : ℂ := ((9 * (Real.sqrt 3 / 2) : ℝ) : ℂ) * (phiG (4 / 3) / 3) with hC
  set a : ℝ → ℂ := fun v => ∫ z in fundP3, thetaF r Y hY (z, v) with ha
  have hcont : ContinuousOn (fun v : ℝ => ((v : ℝ) : ℂ) ^ (-1 - 4 / 3 : ℂ)) (Ioi 0) := fun v hv =>
    (continuousAt_ofReal_cpow_const v _ (Or.inr (show (0 : ℝ) < v from hv).ne')).continuousWithinAt
  have key := ae_eq_of_setIntegral_Icc (f := fun v => ((v ^ (-3 : ℤ) : ℝ) : ℂ) * a v)
    (g := fun v => C * ((v : ℝ) : ℂ) ^ (-1 - 4 / 3 : ℂ)) ?_ ?_ ?_
  · filter_upwards [key, ae_restrict_mem measurableSet_Ioi] with v hv hv0
    have hv0' : (0 : ℝ) < v := hv0
    have hvc : (v : ℂ) ≠ 0 := by exact_mod_cast hv0'.ne'
    have e3 : ((v ^ (-3 : ℤ) : ℝ) : ℂ) = ((v : ℂ) ^ 3)⁻¹ := by
      rw [Complex.ofReal_zpow, zpow_neg]
      norm_cast
    have e7 : ((v : ℝ) : ℂ) ^ (-1 - 4 / 3 : ℂ) = (((v ^ (2 / 3 : ℝ) : ℝ) : ℂ)) * ((v : ℂ) ^ 3)⁻¹ := by
      rw [show (-1 - 4 / 3 : ℂ) = ((2 / 3 : ℝ) : ℂ) - 3 by push_cast; ring,
        Complex.cpow_sub _ _ hvc, ← Complex.ofReal_cpow hv0'.le, div_eq_mul_inv]
      norm_cast
    rw [e3, e7] at hv
    have h3 : (v : ℂ) ^ 3 ≠ 0 := pow_ne_zero 3 hvc
    calc a v = (v : ℂ) ^ 3 * (((v : ℂ) ^ 3)⁻¹ * a v) := by field_simp
      _ = (v : ℂ) ^ 3 * (C * (((v ^ (2 / 3 : ℝ) : ℝ) : ℂ) * ((v : ℂ) ^ 3)⁻¹)) := by rw [hv]
      _ = C * (((v ^ (2 / 3 : ℝ) : ℝ) : ℂ)) := by field_simp
  · intro n
    have hα : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    have hai : IntegrableOn a (Icc (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1)) :=
      integrableOn_slice (integrableOn_thetaF hr hY hα _)
    refine (hai.norm.const_mul ((1 / ((n : ℝ) + 1)) ^ (-3 : ℤ))).mono' ?_ ?_
    · have hc : Measurable fun v : ℝ => ((v ^ (-3 : ℤ) : ℝ) : ℂ) := by fun_prop
      exact hc.aestronglyMeasurable.mul hai.aestronglyMeasurable
    · rw [ae_restrict_iff' measurableSet_Icc]
      refine Eventually.of_forall fun v hv => ?_
      have hv0 : 0 < v := lt_of_lt_of_le hα hv.1
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
      exact mul_le_mul_of_nonneg_right (zpow_neg_three_le hα hv.1) (norm_nonneg _)
  · intro n
    have hα : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    have hsub : Icc (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1) ⊆ Ioi 0 := fun v hv => lt_of_lt_of_le hα hv.1
    exact ((hcont.mono hsub).integrableOn_compact isCompact_Icc).const_mul C
  · intro n S hS hSI
    have hα : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    have hαβ : 1 / ((n : ℝ) + 1) ≤ (n : ℝ) + 1 := by
      have h1n : (1 : ℝ) ≤ (n : ℝ) + 1 := by
        have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
        linarith
      exact ((div_le_one (by positivity)).2 h1n).trans h1n
    have hSsub : S ⊆ Ioi 0 := fun v hv => lt_of_lt_of_le hα (hSI hv).1
    obtain ⟨ψ, hψdef⟩ : ∃ ψ : ℝ → ℂ, ψ = S.indicator fun _ => 1 := ⟨_, rfl⟩
    have hψm : Measurable ψ := by rw [hψdef]; exact measurable_const.indicator hS
    have hψM : ∀ v, ‖ψ v‖ ≤ 1 := fun v => by
      by_cases h : v ∈ S
      · rw [hψdef, indicator_of_mem h, norm_one]
      · rw [hψdef, indicator_of_notMem h, norm_zero]
        norm_num
    have hψ0 : ∀ v, v ∉ Icc (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1) → ψ v = 0 := fun v hv => by
      rw [hψdef, indicator_of_notMem fun h => hv (hSI h)]
    have hψ2 : MemLp (pseis ψ) 2 (muR rhoG) := memLp_pseis_Icc hψm hψM hψ0 hα
    have h1 := inner_pseis_thetaL_unfold hr hY hψm hψ2 hψM hψ0 hα
    have h2 := inner_pseis_thetaL_gen hr hY hψm hψ2 hψM hψ0 hα hαβ
    rw [h1] at h2
    unfold mellinPsi at h2
    have e1 : ∫ v in Ioi 0, ((v ^ (-3 : ℤ) : ℝ) : ℂ) * conj (ψ v) * a v =
        ∫ v in S, ((v ^ (-3 : ℤ) : ℝ) : ℂ) * a v := by
      calc ∫ v in Ioi 0, ((v ^ (-3 : ℤ) : ℝ) : ℂ) * conj (ψ v) * a v
          = ∫ v in Ioi 0, S.indicator (fun v => ((v ^ (-3 : ℤ) : ℝ) : ℂ) * a v) v := by
            refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
            by_cases h : v ∈ S
            · rw [hψdef, indicator_of_mem h, indicator_of_mem h, map_one, mul_one]
            · rw [hψdef, indicator_of_notMem h, indicator_of_notMem h, map_zero, mul_zero, zero_mul]
        _ = ∫ v in Ioi 0 ∩ S, ((v ^ (-3 : ℤ) : ℝ) : ℂ) * a v := setIntegral_indicator hS
        _ = ∫ v in S, ((v ^ (-3 : ℤ) : ℝ) : ℂ) * a v := by rw [inter_eq_right.2 hSsub]
    have e2 : ∫ v in Ioi 0, conj (ψ v) * ((v : ℝ) : ℂ) ^ (-1 - 4 / 3 : ℂ) =
        ∫ v in S, ((v : ℝ) : ℂ) ^ (-1 - 4 / 3 : ℂ) := by
      calc ∫ v in Ioi 0, conj (ψ v) * ((v : ℝ) : ℂ) ^ (-1 - 4 / 3 : ℂ)
          = ∫ v in Ioi 0, S.indicator (fun v => ((v : ℝ) : ℂ) ^ (-1 - 4 / 3 : ℂ)) v := by
            refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
            by_cases h : v ∈ S
            · rw [hψdef, indicator_of_mem h, indicator_of_mem h, map_one, one_mul]
            · rw [hψdef, indicator_of_notMem h, indicator_of_notMem h, map_zero, zero_mul]
        _ = ∫ v in Ioi 0 ∩ S, ((v : ℝ) : ℂ) ^ (-1 - 4 / 3 : ℂ) := setIntegral_indicator hS
        _ = ∫ v in S, ((v : ℝ) : ℂ) ^ (-1 - 4 / 3 : ℂ) := by rw [inter_eq_right.2 hSsub]
    rw [e1, e2] at h2
    rw [h2, integral_const_mul]

end Eis

end

#print axioms Eis.setLIntegral_lt_top_of_bdd
#print axioms Eis.lintegral_rhoT3_ps_ne_top
#print axioms Eis.inner_pseis_uL_band
#print axioms Eis.inner_pseis_thetaL_gen
#print axioms Eis.integrableOn_thetaF
#print axioms Eis.inner_pseis_thetaL_unfold
#print axioms Eis.ae_eq_of_setIntegral_Icc
#print axioms Eis.const_thetaF_ae
