import KubotaCuspIdent

/-! # θ's coefficients at the cusps `γ_t` (round 464)

S5f-15 of round 360's plan, part 5. Round 463's next step planned θ's Fourier coefficients at the cusp `γ_t`
from round 463's relation between the pairings with `ũ_s`. This round proves them, for `tt′ = 1`, `m ≠ 0` in
the class of the cusp `γ_t` (round 461's `CuspClass`), `λ = ω − 1`, `m′ = δ₃ω²tλ²m` and `ψ̃(v) = ψ(3√3·v)`. In
a pointwise formula `θ` is round 436's Fourier series `thS`, which round 437 showed equal to θ almost
everywhere (`thSU` is its extension by `0` off upper half-space, round 461):

* **The function `A_y`** (`aBand`, a definition; **`differentiableOn_aBand`** and **`tendsto_aBand`**):
  `A_y(s) = ⟨y, ũ_s⟩ + ⟨y, E(1[Y ≤ v ≤ H]v^s)⟩` is holomorphic on round 427's `U`, and
  `iε·A_y(4/3 + iε) → ⟨y, θ⟩` as `ε → 0⁺` (round 425's `tendsto_uL_thetaL`).
* **θ at the cusp `0` in `L²(ν)`** (**`inner_comp_sS_inv_thetaL`**): `⟨u∘S⁻¹, θ⟩ = ⟨u, θ⟩` for `u` measurable
  and automorphic with Kubota's character, with `u` and `u∘S⁻¹` in `L²(ν)` (round 442's
  `integral_conj_sS_inv_mul`, round 443's `thetaF_sS_ae`).
* **The residue relation** (**`residue_eq_of_eq_cpow`**): if `A₁` and `A₂` are holomorphic on `U`,
  `A₁(s) = ζ·c^{−s}·A₂(s)` where `Re s > 2` for some `c ≠ 0`, and `iε·A_i(4/3 + iε) → a_i`, then
  `a₁ = ζ·c^{−4/3}·a₂` (the identity theorem on `U`, as in round 431's `inner_pmSer_thetaL_cross`).
* **θ's pairing at `γ_t`** (`rhoCusp`, a definition; **`aBand_pmSerC_eq`**, **`inner_pmSerC_thetaL_eq`**,
  **`inner_pmSerS_thetaL`** and **`inner_pmSerC_thetaL_rho`**, with `cuspIdx_ne_zero` and `sqrt27_cpow`): for
  `ψ` measurable and bounded, vanishing outside `[α, β]` with `0 < α ≤ β`,
  `⟨Q_t(ψ), θ⟩ = ĕ(mt′/9)·(3√3)^{−4/3}·⟨P_{m′}(ψ̃)∘S⁻¹, θ⟩` (round 463's `inner_pmSerC_uL_eq`),
  `⟨P_{m′}(ψ̃)∘S⁻¹, θ⟩ = ρ(m′)·J_{ψ̃}(4/3)` (round 431's `inner_pmSer_thetaL`), and so
  `⟨Q_t(ψ), θ⟩ = ρ_t(m)·J_ψ(4/3)` with `ρ_t(m) = ĕ(mt′/9)·3^{−1/2}·ρ(m′)` (round 463's `norm_σO_cuspIdx` and
  `jPsi_comp_mul`).
* **The coefficients** (**`inner_pmSerC_thetaL_unfold`**, **`coef_lowT_ae`**, **`continuousOn_coef_lowT`** and
  **`coef_lowT`**, with `integrableOn_ebr_thSU_lowT`):
  `⟨Q_t(ψ), θ⟩ = ∫_0^∞ v^{−3}·conj ψ(v)·∫_{3P} ĕ(−mz/9)·θ(γ_t(z, v)) dz dv` (round 461's
  `inner_pmSerC_thetaL`, round 430's `integral_fundP3_conj_mul`), so for almost every `v > 0` (the profiles
  `1_S`, as in round 432's `coef_thetaF_ae`), and then for every `v > 0` (both sides continuous, the left by
  dominated convergence), `∫_{3P} ĕ(−mz/9)·θ(γ_t(z, v)) dz = ρ_t(m)·v·K_{1/3}(4π|m|v/9)`.
-/

open MeasureTheory Set Filter NumberField Complex Ideal Asymptotics
open scoped ENNReal Topology MatrixGroups ComplexConjugate

noncomputable section

namespace Eis

/-! ### The pairing with `ũ_s` plus a band term -/

/-- `A_y(s) = ⟨y, ũ_s⟩ + ⟨y, E(1[Y ≤ v ≤ H]v^s)⟩`. -/
def aBand (r Y : ℝ) (hY : 0 < Y) {H : ℝ} (hYH : Y ≤ H) (y : Lp ℂ 2 (muR rhoG)) (s : ℂ) : ℂ :=
  inner ℂ y (uL (2 * Real.cosh r - 2) (cosh_sub_nonneg r) Y hY s) + inner ℂ y (bandL hY hYH s)

/-- `A_y` is holomorphic on round 427's `U` (round 424's `differentiableAt_inner_uL`, round 430's
`differentiable_inner_bandL`). -/
theorem differentiableOn_aBand {r : ℝ} (hr : 0 < r) {Y : ℝ} (hY : 0 < Y) {H : ℝ} (hYH : Y ≤ H)
    (y : Lp ℂ 2 (muR rhoG)) : DifferentiableOn ℂ (aBand r Y hY hYH y) (domU r) := by
  intro s hs
  have him : (hhat (2 * Real.cosh r - 2) s).im ≠ 0 :=
    (im_hhat_pos hr hs.1 hs.2.1 ((lt_div_iff₀ hr).1 hs.2.2)).ne'
  exact ((differentiableAt_inner_uL hr.le hY y him).add
    (differentiable_inner_bandL y hY hYH s)).differentiableWithinAt

/-- **The residue of `A_y`**: `iε·A_y(4/3 + iε) → ⟨y, θ⟩` as `ε → 0⁺` (round 425's `tendsto_uL_thetaL`). -/
theorem tendsto_aBand {r : ℝ} (hr : 0 < r) {Y : ℝ} (hY : 0 < Y) {H : ℝ} (hYH : Y ≤ H)
    (y : Lp ℂ 2 (muR rhoG)) :
    Tendsto (fun ε : ℝ => (I * ε) * aBand r Y hY hYH y (((4 / 3 : ℝ) : ℂ) + I * ε)) (𝓝[>] 0)
      (𝓝 (inner ℂ y (thetaL r Y hY))) := by
  have hγ : Tendsto (fun ε : ℝ => ((4 / 3 : ℝ) : ℂ) + I * ε) (𝓝[>] 0) (𝓝 ((4 / 3 : ℝ) : ℂ)) := by
    have hc : Continuous fun ε : ℝ => ((4 / 3 : ℝ) : ℂ) + I * ε := by fun_prop
    have := hc.tendsto 0
    simp only [ofReal_zero, mul_zero, add_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hI : Tendsto (fun ε : ℝ => I * (ε : ℂ)) (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous fun ε : ℝ => I * (ε : ℂ) := by fun_prop
    have := hc.tendsto 0
    simp only [ofReal_zero, mul_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hL : Tendsto (fun ε : ℝ => (I * ε) *
      inner ℂ y (uL (2 * Real.cosh r - 2) (cosh_sub_nonneg r) Y hY (((4 / 3 : ℝ) : ℂ) + I * ε)))
      (𝓝[>] 0) (𝓝 (inner ℂ y (thetaL r Y hY))) := by
    have h := ((innerSL ℂ y).continuous.tendsto _).comp (tendsto_uL_thetaL hr hY)
    refine h.congr fun ε => ?_
    simp only [Function.comp, innerSL_apply_apply, inner_smul_right]
  have h3 : Tendsto (fun ε : ℝ => inner ℂ y (bandL hY hYH (((4 / 3 : ℝ) : ℂ) + I * ε))) (𝓝[>] 0)
      (𝓝 (inner ℂ y (bandL hY hYH ((4 / 3 : ℝ) : ℂ)))) :=
    (differentiable_inner_bandL y hY hYH _).continuousAt.tendsto.comp hγ
  have h := hL.add (hI.mul h3)
  simp only [zero_mul, add_zero] at h
  refine h.congr fun ε => ?_
  unfold aBand
  ring

/-! ### θ at the cusp `0` in `L²(ν)` -/

/-- **`⟨u∘S⁻¹, θ⟩ = ⟨u, θ⟩`** for `u` measurable and automorphic with Kubota's character, with `u` and `u∘S⁻¹`
in `L²(ν)` (round 442's `integral_conj_sS_inv_mul`, round 443's `thetaF_sS_ae`). -/
theorem inner_comp_sS_inv_thetaL {u : ℂ × ℝ → ℂ} (hum : Measurable u)
    (hu : IsAut Gam3 (fun g => kub ↑g) u) (hu2 : MemLp u 2 (muR rhoG))
    (hS2 : MemLp (fun p => u (slAct sS⁻¹ p)) 2 (muR rhoG)) {r : ℝ} (hr : 0 < r) {Y : ℝ} (hY : 0 < Y) :
    inner ℂ (hS2.toLp fun p => u (slAct sS⁻¹ p)) (thetaL r Y hY) = inner ℂ (hu2.toLp u) (thetaL r Y hY) := by
  have hθ2 := memLp_thetaF hr hY
  have hθ : thetaL r Y hY = hθ2.toLp (thetaF r Y hY) :=
    Lp.ext ((thetaL_ae_eq_thetaF hr hY).trans hθ2.coeFn_toLp.symm)
  have hint : ∫⁻ p, ‖conj (u (slAct sS⁻¹ p)) * thetaF r Y hY p‖ₑ ∂(muR rhoG) < ⊤ := by
    have h1 : MemLp (fun p => conj (u (slAct sS⁻¹ p))) 2 (muR rhoG) :=
      hS2.of_le ((Complex.continuous_conj.measurable.comp
        (hum.comp (measurable_slAct _))).aestronglyMeasurable)
        (Eventually.of_forall fun p => by rw [Complex.norm_conj])
    exact (h1.integrable_mul hθ2).2
  have hSae : ∀ᵐ p ∂(muR rhoG), thetaF r Y hY (slAct sS p) = thetaF r Y hY p :=
    withDensity_absolutelyContinuous uhsMeasure rhoG (thetaF_sS_ae hr hY)
  rw [hθ, L2.inner_def, L2.inner_def]
  calc ∫ p, inner ℂ ((hS2.toLp fun p => u (slAct sS⁻¹ p)) p) ((hθ2.toLp (thetaF r Y hY)) p) ∂(muR rhoG)
      = ∫ p, conj (u (slAct sS⁻¹ p)) * thetaF r Y hY p ∂(muR rhoG) := by
        refine integral_congr_ae ?_
        filter_upwards [hS2.coeFn_toLp, hθ2.coeFn_toLp] with p h1 h2
        rw [RCLike.inner_apply', h1, h2]
    _ = ∫ p, conj (u p) * thetaF r Y hY (slAct sS p) ∂(muR rhoG) :=
        integral_conj_sS_inv_mul hum (measurable_thetaF r Y hY) hu (isAut_thetaF r Y hY) hint
    _ = ∫ p, conj (u p) * thetaF r Y hY p ∂(muR rhoG) := by
        refine integral_congr_ae ?_
        filter_upwards [hSae] with p hp
        rw [hp]
    _ = ∫ p, inner ℂ ((hu2.toLp u) p) ((hθ2.toLp (thetaF r Y hY)) p) ∂(muR rhoG) := by
        refine integral_congr_ae ?_
        filter_upwards [hu2.coeFn_toLp, hθ2.coeFn_toLp] with p h1 h2
        rw [RCLike.inner_apply', h1, h2]

/-! ### The residue relation -/

/-- **Residues of related functions**: if `A₁` and `A₂` are holomorphic on round 427's `U`, satisfy
`A₁(s) = ζ·c^{−s}·A₂(s)` where `Re s > 2`, and `iε·A_i(4/3 + iε)` tends to `a_i` as `ε → 0⁺`, then
`a₁ = ζ·c^{−4/3}·a₂` (the identity theorem on `U`, which is connected). -/
theorem residue_eq_of_eq_cpow {r : ℝ} (hr : 0 < r) {A₁ A₂ : ℂ → ℂ} (h₁ : DifferentiableOn ℂ A₁ (domU r))
    (h₂ : DifferentiableOn ℂ A₂ (domU r)) {ζ c : ℂ} (hc : c ≠ 0)
    (hA : ∀ s, s ∈ domU r → 2 < s.re → A₁ s = ζ * c ^ (-s) * A₂ s) {a₁ a₂ : ℂ}
    (ha₁ : Tendsto (fun ε : ℝ => (I * ε) * A₁ (((4 / 3 : ℝ) : ℂ) + I * ε)) (𝓝[>] 0) (𝓝 a₁))
    (ha₂ : Tendsto (fun ε : ℝ => (I * ε) * A₂ (((4 / 3 : ℝ) : ℂ) + I * ε)) (𝓝[>] 0) (𝓝 a₂)) :
    a₁ = ζ * c ^ (-(4 / 3 : ℂ)) * a₂ := by
  have hcd : Differentiable ℂ fun s : ℂ => c ^ (-s) := fun s =>
    differentiableAt_id.neg.const_cpow (Or.inl hc)
  set F : ℂ → ℂ := fun s => A₁ s - ζ * c ^ (-s) * A₂ s with hF
  have hFd : DifferentiableOn ℂ F (domU r) :=
    h₁.sub (((differentiableOn_const ζ).mul hcd.differentiableOn).mul h₂)
  -- `F = 0` where `Re s > 2`
  obtain ⟨t, htdef⟩ : ∃ t : ℝ, t = Real.pi / (2 * r) := ⟨_, rfl⟩
  have ht0 : 0 < t := by rw [htdef]; positivity
  have htr : t < Real.pi / r := by
    rw [htdef, div_lt_div_iff₀ (by positivity) hr]
    nlinarith [Real.pi_pos]
  set z0 : ℂ := 3 + I * (t : ℂ) with hz0def
  have hz0re : z0.re = 3 := by simp [z0]
  have hz0im : z0.im = t := by simp [z0]
  have hz0 : z0 ∈ domU r := by
    refine ⟨?_, ?_, ?_⟩
    · show 1 < z0.re
      rw [hz0re]
      norm_num
    · show 0 < z0.im
      rw [hz0im]
      exact ht0
    · show z0.im < Real.pi / r
      rw [hz0im]
      exact htr
  have hfg : F =ᶠ[𝓝 z0] fun _ => 0 := by
    have hO : IsOpen (domU r ∩ {s | 2 < s.re}) :=
      (isOpen_domU r).inter (isOpen_lt continuous_const continuous_re)
    have hmem : z0 ∈ domU r ∩ {s | 2 < s.re} := ⟨hz0, by show 2 < z0.re; rw [hz0re]; norm_num⟩
    filter_upwards [hO.mem_nhds hmem] with s hs
    simp only [hF]
    rw [hA s hs.1 hs.2, sub_self]
  have heq : EqOn F (fun _ => 0) (domU r) :=
    (hFd.analyticOnNhd (isOpen_domU r)).eqOn_of_preconnected_of_eventuallyEq
      analyticOnNhd_const (convex_domU r).isPreconnected hz0 hfg
  -- the residue
  have hγ : Tendsto (fun ε : ℝ => ((4 / 3 : ℝ) : ℂ) + I * ε) (𝓝[>] 0) (𝓝 ((4 / 3 : ℝ) : ℂ)) := by
    have hc : Continuous fun ε : ℝ => ((4 / 3 : ℝ) : ℂ) + I * ε := by fun_prop
    have := hc.tendsto 0
    simp only [ofReal_zero, mul_zero, add_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hγU : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ((4 / 3 : ℝ) : ℂ) + I * (ε : ℂ) ∈ domU r := by
    filter_upwards [Ioo_mem_nhdsGT (div_pos Real.pi_pos hr)] with ε hε
    refine ⟨?_, ?_, ?_⟩
    · show 1 < (((4 / 3 : ℝ) : ℂ) + I * ε).re
      simp
      norm_num
    · show 0 < (((4 / 3 : ℝ) : ℂ) + I * ε).im
      simp [hε.1]
    · show (((4 / 3 : ℝ) : ℂ) + I * ε).im < Real.pi / r
      simp [hε.2]
  have hct : Tendsto (fun ε : ℝ => c ^ (-(((4 / 3 : ℝ) : ℂ) + I * ε))) (𝓝[>] 0)
      (𝓝 (c ^ (-((4 / 3 : ℝ) : ℂ)))) :=
    (hcd _).continuousAt.tendsto.comp hγ
  have hlim := ha₁.sub ((tendsto_const_nhds (x := ζ)).mul (hct.mul ha₂))
  have h0 : Tendsto (fun ε : ℝ => (I * ε) * A₁ (((4 / 3 : ℝ) : ℂ) + I * ε) -
      ζ * (c ^ (-(((4 / 3 : ℝ) : ℂ) + I * ε)) * ((I * ε) * A₂ (((4 / 3 : ℝ) : ℂ) + I * ε))))
      (𝓝[>] 0) (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hγU] with ε hε
    have := heq hε
    simp only [hF] at this
    linear_combination (-(I * (ε : ℂ))) * this
  have hfin := tendsto_nhds_unique hlim h0
  have e43 : ((4 / 3 : ℝ) : ℂ) = 4 / 3 := by push_cast; ring
  rw [e43] at hfin
  linear_combination hfin

/-! ### θ's pairing with the Poincaré series at `γ_t` -/

/-- Round 463's relation in terms of `A_y`: for `Re s > 2`,
`A_{Q_t(ψ)}(s) = ĕ(mt′/9)·(3√3)^{−s}·A_{P_{m′}(ψ̃)∘S⁻¹}(s)`. -/
theorem aBand_pmSerC_eq {t t' m : 𝓞 K} (htt : t * t' = 1) (hm : CuspClass t m) (hm0 : m ≠ 0)
    {r Y : ℝ} (hY : 0 < Y) {ψ : ℝ → ℂ} (hψ : Measurable ψ) {M α β : ℝ}
    (hM : ∀ v, ‖ψ v‖ ≤ M) (hψ0 : ∀ v, v ∉ Icc α β → ψ v = 0) (hα : 0 < α) (hαβ : α ≤ β) {s : ℂ}
    (hs : 2 < s.re) (him : (hhat (2 * Real.cosh r - 2) s).im ≠ 0) :
    aBand r Y hY (le_band hα hαβ) ((memLp_pmSerC_Icc t m hψ hM hψ0 hα).toLp (pmSerC t m ψ)) s =
      ebr (σO m * σO t' / 9) * ((3 * Real.sqrt 3 : ℝ) : ℂ) ^ (-s) *
        aBand r Y hY (le_band (div_pos hα sqrt27_pos) (div_le_div_of_nonneg_right hαβ sqrt27_pos.le))
          ((memLp_pmSerS (measurable_sclPsi hψ) (memLp_pmSer_Icc (δ3 * (ω ^ 2 * t * (ω - 1) ^ 2 * m))
            (measurable_sclPsi hψ) (norm_sclPsi_le hM) (sclPsi_eq_zero hψ0)
            (div_pos hα sqrt27_pos))).toLp (pmSerS (δ3 * (ω ^ 2 * t * (ω - 1) ^ 2 * m)) (sclPsi ψ))) s :=
  inner_pmSerC_uL_eq htt hm hm0 (cosh_sub_nonneg r) hY hψ hM hψ0 hα hαβ hs him

/-- **θ at `γ_t` through the cusp `0`**: for `tt′ = 1`, `m ≠ 0` in the class of `t`, `r, Y > 0`, and `ψ`
measurable and bounded, vanishing outside `[α, β]` with `0 < α ≤ β`,
`⟨Q_t(ψ), θ⟩ = ĕ(mt′/9)·(3√3)^{−4/3}·⟨P_{m′}(ψ̃)∘S⁻¹, θ⟩` with `m′ = δ₃ω²tλ²m` and `ψ̃(v) = ψ(3√3v)`
(`residue_eq_of_eq_cpow` with `aBand_pmSerC_eq`, and `tendsto_aBand`). -/
theorem inner_pmSerC_thetaL_eq {t t' m : 𝓞 K} (htt : t * t' = 1) (hm : CuspClass t m) (hm0 : m ≠ 0)
    {r : ℝ} (hr : 0 < r) {Y : ℝ} (hY : 0 < Y) {ψ : ℝ → ℂ} (hψ : Measurable ψ) {M α β : ℝ}
    (hM : ∀ v, ‖ψ v‖ ≤ M) (hψ0 : ∀ v, v ∉ Icc α β → ψ v = 0) (hα : 0 < α) (hαβ : α ≤ β) :
    inner ℂ ((memLp_pmSerC_Icc t m hψ hM hψ0 hα).toLp (pmSerC t m ψ)) (thetaL r Y hY) =
      ebr (σO m * σO t' / 9) * ((3 * Real.sqrt 3 : ℝ) : ℂ) ^ (-(4 / 3 : ℂ)) *
        inner ℂ ((memLp_pmSerS (measurable_sclPsi hψ) (memLp_pmSer_Icc (δ3 * (ω ^ 2 * t * (ω - 1) ^ 2 * m))
            (measurable_sclPsi hψ) (norm_sclPsi_le hM) (sclPsi_eq_zero hψ0)
            (div_pos hα sqrt27_pos))).toLp (pmSerS (δ3 * (ω ^ 2 * t * (ω - 1) ^ 2 * m)) (sclPsi ψ)))
          (thetaL r Y hY) :=
  residue_eq_of_eq_cpow hr (differentiableOn_aBand hr hY _ _) (differentiableOn_aBand hr hY _ _)
    (by exact_mod_cast sqrt27_pos.ne')
    (fun s hs hs2 => aBand_pmSerC_eq htt hm hm0 hY hψ hM hψ0 hα hαβ hs2
      (im_hhat_pos hr hs.1 hs.2.1 ((lt_div_iff₀ hr).1 hs.2.2)).ne')
    (tendsto_aBand hr hY _ _) (tendsto_aBand hr hY _ _)

/-- **`⟨P_m(ψ)∘S⁻¹, θ⟩ = ρ(m)·J_ψ(4/3)`** for `m = δ₃x ≠ 0` (`inner_comp_sS_inv_thetaL`, round 431's
`inner_pmSer_thetaL`). -/
theorem inner_pmSerS_thetaL {x : 𝓞 K} (hx : x ≠ 0) {r : ℝ} (hr : 0 < r) {Y : ℝ} (hY : 0 < Y)
    {ψ : ℝ → ℂ} (hψ : Measurable ψ) (hψ2 : MemLp (pmSer (δ3 * x) ψ) 2 (muR rhoG)) {M α β : ℝ}
    (hM : ∀ v, ‖ψ v‖ ≤ M) (hψ0 : ∀ v, v ∉ Icc α β → ψ v = 0) (hα : 0 < α) (hαβ : α ≤ β) :
    inner ℂ ((memLp_pmSerS hψ hψ2).toLp (pmSerS (δ3 * x) ψ)) (thetaL r Y hY) =
      rhoM x r Y hY * jPsi (4 * Real.pi * ‖σO (δ3 * x) / 9‖) ψ (4 / 3) :=
  (inner_comp_sS_inv_thetaL (measurable_pmSer _ hψ) (isAut_pmSer x ψ) hψ2 (memLp_pmSerS hψ hψ2) hr
    hY).trans (inner_pmSer_thetaL hx hr hY hψ hψ2 hM hψ0 hα hαβ)

/-! ### θ's coefficients at `γ_t` -/

/-- `m′ = ω²tλ²m ≠ 0` for `t` a unit and `m ≠ 0`. -/
theorem cuspIdx_ne_zero {t t' m : 𝓞 K} (htt : t * t' = 1) (hm0 : m ≠ 0) :
    ω ^ 2 * t * (ω - 1) ^ 2 * m ≠ 0 := by
  have ht0 : t ≠ 0 := left_ne_zero_of_mul_eq_one htt
  have hω0 : ω ≠ 0 := by rw [← coe_ωu]; exact ωu.ne_zero
  have hl0 : (ω - 1 : 𝓞 K) ≠ 0 := fun h => by
    have := normSq_σO_lam; rw [h, map_zero, Complex.normSq_zero] at this; norm_num at this
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hω0) ht0) (pow_ne_zero 2 hl0)) hm0

/-- `(3√3)^{−4/3}·3√3 = 3^{−1/2}`. -/
theorem sqrt27_cpow : ((3 * Real.sqrt 3 : ℝ) : ℂ) ^ (-(4 / 3 : ℂ)) * ((3 * Real.sqrt 3 : ℝ) : ℂ) =
    (((Real.sqrt 3)⁻¹ : ℝ) : ℂ) := by
  have e : (-(4 / 3 : ℂ)) = ((-(4 / 3) : ℝ) : ℂ) := by push_cast; ring
  rw [e, ← Complex.ofReal_cpow sqrt27_pos.le, ← Complex.ofReal_mul]
  congr 1
  have h3 : 3 * Real.sqrt 3 = Real.sqrt 3 ^ 3 := by rw [pow_succ, Real.sq_sqrt (by norm_num)]
  calc (3 * Real.sqrt 3) ^ (-(4 / 3) : ℝ) * (3 * Real.sqrt 3) = (3 * Real.sqrt 3) ^ (-(1 / 3) : ℝ) := by
        rw [← Real.rpow_add_one sqrt27_pos.ne']
        norm_num
    _ = (Real.sqrt 3)⁻¹ := by
        rw [h3, ← Real.rpow_natCast_mul (Real.sqrt_nonneg 3)]
        norm_num [Real.rpow_neg_one]

/-- **θ's coefficient at `γ_t`**: `ĕ(mt′/9)·3^{−1/2}·ρ(m′)` with `m′ = δ₃ω²tλ²m` and round 431's `rhoM`. -/
def rhoCusp (t t' m : 𝓞 K) (r Y : ℝ) (hY : 0 < Y) : ℂ :=
  ebr (σO m * σO t' / 9) * (((Real.sqrt 3)⁻¹ : ℝ) : ℂ) * rhoM (ω ^ 2 * t * (ω - 1) ^ 2 * m) r Y hY

/-- **The pairing of θ with `Q_t(ψ)`**: for `tt′ = 1`, `m ≠ 0` in the class of `t`, `r, Y > 0`, and `ψ`
measurable and bounded, vanishing outside `[α, β]` with `0 < α ≤ β`, `⟨Q_t(ψ), θ⟩ = ρ_t(m)·J_ψ(4/3)` with
`ρ_t(m) = ĕ(mt′/9)·3^{−1/2}·ρ(m′)` (`inner_pmSerC_thetaL_eq`, `inner_pmSerS_thetaL`, round 463's
`norm_σO_cuspIdx` and `jPsi_comp_mul`). -/
theorem inner_pmSerC_thetaL_rho {t t' m : 𝓞 K} (htt : t * t' = 1) (hm : CuspClass t m) (hm0 : m ≠ 0)
    {r : ℝ} (hr : 0 < r) {Y : ℝ} (hY : 0 < Y) {ψ : ℝ → ℂ} (hψ : Measurable ψ) {M α β : ℝ}
    (hM : ∀ v, ‖ψ v‖ ≤ M) (hψ0 : ∀ v, v ∉ Icc α β → ψ v = 0) (hα : 0 < α) (hαβ : α ≤ β) :
    inner ℂ ((memLp_pmSerC_Icc t m hψ hM hψ0 hα).toLp (pmSerC t m ψ)) (thetaL r Y hY) =
      rhoCusp t t' m r Y hY * jPsi (4 * Real.pi * ‖σO m / 9‖) ψ (4 / 3) := by
  rw [inner_pmSerC_thetaL_eq htt hm hm0 hr hY hψ hM hψ0 hα hαβ,
    inner_pmSerS_thetaL (cuspIdx_ne_zero htt hm0) hr hY (measurable_sclPsi hψ)
      (memLp_pmSer_Icc (δ3 * (ω ^ 2 * t * (ω - 1) ^ 2 * m)) (measurable_sclPsi hψ) (norm_sclPsi_le hM)
        (sclPsi_eq_zero hψ0) (div_pos hα sqrt27_pos))
      (norm_sclPsi_le hM) (sclPsi_eq_zero hψ0) (div_pos hα sqrt27_pos)
      (div_le_div_of_nonneg_right hαβ sqrt27_pos.le),
    norm_σO_cuspIdx htt,
    show 4 * Real.pi * (3 * Real.sqrt 3 * ‖σO m / 9‖) = 3 * Real.sqrt 3 * (4 * Real.pi * ‖σO m / 9‖) by ring,
    show sclPsi ψ = fun v => ψ (3 * Real.sqrt 3 * v) from rfl, jPsi_comp_mul sqrt27_pos]
  unfold rhoCusp
  rw [← sqrt27_cpow]
  ring

/-- **The pairing of `Q_t(ψ)` with θ, unfolded**: for `ψ` measurable and bounded, vanishing outside `[α, β]`
with `α > 0`, `⟨Q_t(ψ), θ⟩ = ∫_0^∞ v^{−3}·conj ψ(v)·∫_{3P} ĕ(−mz/9)θ(γ_t(z, v)) dz dv` with θ's Fourier series
(round 461's `inner_pmSerC_thetaL`, round 430's `integral_fundP3_conj_mul`). -/
theorem inner_pmSerC_thetaL_unfold {r : ℝ} (hr : 0 < r) {Y : ℝ} (hY : 0 < Y) {t m : 𝓞 K} (hm : CuspClass t m)
    {ψ : ℝ → ℂ} (hψ : Measurable ψ) {M α β : ℝ} (hM : ∀ v, ‖ψ v‖ ≤ M) (hψ0 : ∀ v, v ∉ Icc α β → ψ v = 0)
    (hα : 0 < α) :
    inner ℂ ((memLp_pmSerC_Icc t m hψ hM hψ0 hα).toLp (pmSerC t m ψ)) (thetaL r Y hY) =
      ∫ v in Ioi 0, ((v ^ (-3 : ℤ) : ℝ) : ℂ) * conj (ψ v) *
        ∫ z in fundP3, ebr (-(σO m / 9 * z)) * thSU r Y hY (slAct (lowT t) (z, v)) := by
  obtain ⟨B, hB⟩ := exists_bound_thS_lowT hr hY t hα (β := β)
  set F : ℂ × ℝ → ℂ := fun p => conj (ebr (σO m * p.1 / 9)) * thSU r Y hY (slAct (lowT t) p) with hF
  have hFm : Measurable F := by
    have hme : Measurable fun p : ℂ × ℝ => conj (ebr (σO m * p.1 / 9)) :=
      Complex.continuous_conj.measurable.comp
        (measurable_ebr.comp ((measurable_const.mul measurable_fst).div_const 9))
    exact hme.mul ((measurable_thSU hr hY).comp (measurable_slAct _))
  have hFB : ∀ p : ℂ × ℝ, p.1 ∈ fundP3 → p.2 ∈ Icc α β → ‖F p‖ ≤ B := fun p h1 h2 => by
    simp only [hF]
    rw [norm_mul, Complex.norm_conj, norm_ebr, one_mul]
    exact hB p h1 h2
  rw [inner_pmSerC_thetaL hr hY hm hψ hM hψ0 hα]
  have e1 : ∫ p in Prod.fst ⁻¹' fundP3, conj (ψ p.2 * ebr (σO m * p.1 / 9)) * thS r Y hY (slAct (lowT t) p)
      ∂uhsMeasure = ∫ p in Prod.fst ⁻¹' fundP3, conj (ψ p.2) * F p ∂uhsMeasure := by
    refine setIntegral_congr_ae (measurableSet_fundP3.preimage measurable_fst) ?_
    filter_upwards [ae_UHS] with p hp _
    simp only [hF]
    rw [thSU_eq (slAct_mem _ hp), map_mul]
    ring
  rw [e1, integral_fundP3_conj_mul hψ hM hψ0 hα hFm hFB]
  refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
  congr 1
  refine setIntegral_congr_fun measurableSet_fundP3 fun z _ => ?_
  simp only [hF]
  rw [conj_ebr]
  congr 2
  ring

/-- `ĕ(−mz/9)·θ(γ_t(z, v))` is integrable on `3P × [α, β]` for `α > 0` (`exists_bound_thS_lowT`). -/
theorem integrableOn_ebr_thSU_lowT (t m : 𝓞 K) {r : ℝ} (hr : 0 < r) {Y : ℝ} (hY : 0 < Y) {α : ℝ}
    (hα : 0 < α) (β : ℝ) :
    IntegrableOn (fun p : ℂ × ℝ => ebr (-(σO m / 9 * p.1)) * thSU r Y hY (slAct (lowT t) p))
      (fundP3 ×ˢ Icc α β) := by
  obtain ⟨B, hB⟩ := exists_bound_thS_lowT hr hY t hα (β := β)
  have hm : Measurable fun p : ℂ × ℝ => ebr (-(σO m / 9 * p.1)) * thSU r Y hY (slAct (lowT t) p) :=
    (measurable_ebr.comp (measurable_const.mul measurable_fst).neg).mul
      ((measurable_thSU hr hY).comp (measurable_slAct _))
  refine Measure.integrableOn_of_bounded ?_ hm.aestronglyMeasurable (M := B) ?_
  · rw [Measure.volume_eq_prod, Measure.prod_prod, volume_fundP3, Real.volume_Icc]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  · rw [ae_restrict_iff' (measurableSet_fundP3.prod measurableSet_Icc)]
    refine Eventually.of_forall fun p hp => ?_
    rw [norm_mul, norm_ebr, one_mul]
    exact hB p hp.1 hp.2

/-- **θ's Fourier coefficients at `γ_t`, almost everywhere**: for `tt′ = 1`, `m ≠ 0` in the class of `t`,
`r > 0` and `Y > 0`, for almost every `v > 0`, `∫_{3P} ĕ(−mz/9)θ(γ_t(z, v)) dz = ρ_t(m)·v·K_{1/3}(4π|m|v/9)`
with θ's Fourier series (as round 432's `coef_thetaF_ae`, from `inner_pmSerC_thetaL_rho` and
`inner_pmSerC_thetaL_unfold` at the profiles `1_S`). -/
theorem coef_lowT_ae {t t' m : 𝓞 K} (htt : t * t' = 1) (hm : CuspClass t m) (hm0 : m ≠ 0) {r : ℝ}
    (hr : 0 < r) {Y : ℝ} (hY : 0 < Y) :
    ∀ᵐ v ∂(volume.restrict (Ioi (0 : ℝ))),
      ∫ z in fundP3, ebr (-(σO m / 9 * z)) * thSU r Y hY (slAct (lowT t) (z, v)) =
        rhoCusp t t' m r Y hY * ((v : ℂ) * besselK (1 / 3) (4 * Real.pi * ‖σO m / 9‖ * v)) := by
  have hξ : σO m / 9 ≠ 0 := div_ne_zero (σO_ne_zero hm0) (by norm_num)
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = 4 * Real.pi * ‖σO m / 9‖ := ⟨_, rfl⟩
  have hApos : 0 < A := by
    have := norm_pos_iff.2 hξ
    rw [hA]
    positivity
  rw [← hA]
  set a : ℝ → ℂ := fun v => ∫ z in fundP3, ebr (-(σO m / 9 * z)) * thSU r Y hY (slAct (lowT t) (z, v))
    with ha
  set ρ := rhoCusp t t' m r Y hY with hρ
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
      integrableOn_slice (integrableOn_ebr_thSU_lowT t m hr hY hα β)
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
    have h1 := inner_pmSerC_thetaL_unfold hr hY hm hψm hψM hψ0 hα (Y := Y)
    have h2 := inner_pmSerC_thetaL_rho htt hm hm0 hr hY hψm hψM hψ0 hα hαβ
    rw [← hA, ← hρ] at h2
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

/-- `v ↦ ∫_{3P} ĕ(−mz/9)θ(γ_t(z, v)) dz` is continuous on `(0, ∞)` with θ's Fourier series (dominated
convergence: `exists_bound_thS_lowT` and round 437's `continuousOn_slAct`). -/
theorem continuousOn_coef_lowT (t m : 𝓞 K) {r : ℝ} (hr : 0 < r) {Y : ℝ} (hY : 0 < Y) :
    ContinuousOn (fun v : ℝ => ∫ z in fundP3, ebr (-(σO m / 9 * z)) * thSU r Y hY (slAct (lowT t) (z, v)))
      (Ioi 0) := by
  have : IsFiniteMeasure (volume.restrict fundP3) :=
    isFiniteMeasure_restrict.2 (by rw [volume_fundP3]; exact ENNReal.ofReal_ne_top)
  have hIcc : ∀ α β : ℝ, 0 < α → ContinuousOn
      (fun v : ℝ => ∫ z in fundP3, ebr (-(σO m / 9 * z)) * thSU r Y hY (slAct (lowT t) (z, v)))
      (Icc α β) := by
    intro α β hα
    obtain ⟨B, hB⟩ := exists_bound_thS_lowT hr hY t hα (β := β)
    refine continuousOn_of_dominated (bound := fun _ => B) ?_ ?_ (integrable_const B) ?_
    · intro v _
      exact ((measurable_ebr.comp (measurable_const.mul measurable_id).neg).mul
        ((measurable_thSU hr hY).comp ((measurable_slAct _).comp
          (measurable_id.prodMk measurable_const)))).aestronglyMeasurable
    · intro v hv
      rw [ae_restrict_iff' measurableSet_fundP3]
      refine Eventually.of_forall fun z hz => ?_
      rw [norm_mul, norm_ebr, one_mul]
      exact hB (z, v) hz hv
    · refine Eventually.of_forall fun z => ?_
      have hU : ∀ v ∈ Icc α β, ((z, v) : ℂ × ℝ) ∈ UHS := fun v hv => lt_of_lt_of_le hα hv.1
      have hc : ContinuousOn (fun v : ℝ => thS r Y hY (slAct (lowT t) (z, v))) (Icc α β) :=
        ((continuousOn_thS hr hY).comp (continuousOn_slAct (lowT t)) fun p hp => slAct_mem _ hp).comp
          (continuous_const.prodMk continuous_id).continuousOn hU
      refine continuousOn_const.mul (hc.congr fun v hv => ?_)
      exact thSU_eq (slAct_mem _ (hU v hv))
  intro v hv
  have hv0 : (0 : ℝ) < v := hv
  have hn : Icc (v / 2) (2 * v) ∈ 𝓝 v := Icc_mem_nhds (by linarith) (by linarith)
  exact ((hIcc (v / 2) (2 * v) (by positivity)).continuousAt hn).continuousWithinAt

/-- **θ's Fourier coefficients at `γ_t`**: for `tt′ = 1`, `m ≠ 0` in the class of `t`, `r > 0`, `Y > 0` and
every `v > 0`, `∫_{3P} ĕ(−mz/9)θ(γ_t(z, v)) dz = ρ_t(m)·v·K_{1/3}(4π|m|v/9)` with θ's Fourier series
(`coef_lowT_ae`, both sides continuous on `(0, ∞)`). -/
theorem coef_lowT {t t' m : 𝓞 K} (htt : t * t' = 1) (hm : CuspClass t m) (hm0 : m ≠ 0) {r : ℝ}
    (hr : 0 < r) {Y : ℝ} (hY : 0 < Y) {v : ℝ} (hv : 0 < v) :
    ∫ z in fundP3, ebr (-(σO m / 9 * z)) * thS r Y hY (slAct (lowT t) (z, v)) =
      rhoCusp t t' m r Y hY * ((v : ℂ) * besselK (1 / 3) (4 * Real.pi * ‖σO m / 9‖ * v)) := by
  have hξ : σO m / 9 ≠ 0 := div_ne_zero (σO_ne_zero hm0) (by norm_num)
  have hA : 0 < 4 * Real.pi * ‖σO m / 9‖ := by
    have := norm_pos_iff.2 hξ
    positivity
  have e : ∫ z in fundP3, ebr (-(σO m / 9 * z)) * thS r Y hY (slAct (lowT t) (z, v)) =
      ∫ z in fundP3, ebr (-(σO m / 9 * z)) * thSU r Y hY (slAct (lowT t) (z, v)) := by
    refine setIntegral_congr_fun measurableSet_fundP3 fun z _ => ?_
    rw [thSU_eq (slAct_mem _ (show ((z, v) : ℂ × ℝ) ∈ UHS from hv))]
  rw [e]
  have hc2 : ContinuousOn (fun v : ℝ => rhoCusp t t' m r Y hY *
      ((v : ℂ) * besselK (1 / 3) (4 * Real.pi * ‖σO m / 9‖ * v))) (Ioi 0) := by
    intro w hw
    have hw0 : (0 : ℝ) < w := hw
    have hK : ContinuousAt (fun v : ℝ => besselK (1 / 3) (4 * Real.pi * ‖σO m / 9‖ * v)) w :=
      (continuousAt_besselK _ (mul_pos hA hw0)).comp (continuousAt_const.mul continuousAt_id)
    exact (continuousAt_const.mul (Complex.continuous_ofReal.continuousAt.mul hK)).continuousWithinAt
  exact Measure.eqOn_open_of_ae_eq (coef_lowT_ae htt hm hm0 hr hY) isOpen_Ioi
    (continuousOn_coef_lowT t m hr hY) hc2 hv

end Eis

end

#print axioms Eis.differentiableOn_aBand
#print axioms Eis.tendsto_aBand
#print axioms Eis.inner_comp_sS_inv_thetaL
#print axioms Eis.residue_eq_of_eq_cpow
#print axioms Eis.aBand_pmSerC_eq
#print axioms Eis.inner_pmSerC_thetaL_eq
#print axioms Eis.inner_pmSerS_thetaL
#print axioms Eis.cuspIdx_ne_zero
#print axioms Eis.sqrt27_cpow
#print axioms Eis.inner_pmSerC_thetaL_rho
#print axioms Eis.inner_pmSerC_thetaL_unfold
#print axioms Eis.integrableOn_ebr_thSU_lowT
#print axioms Eis.coef_lowT_ae
#print axioms Eis.continuousOn_coef_lowT
#print axioms Eis.coef_lowT
