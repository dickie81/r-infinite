import KubotaCubeCoef

/-! # θ's coefficients as residues (round 450)

S5f-13 of round 360's plan, part 1. Round 449's next step planned `ρ(m)` as a residue of round 430's Dirichlet
series `D_m(s) = Σ_c S_m(c)N(c)^{−s}`, as the first step toward the support condition of round 361's
`ThetaSupp` away from `λ`. This round proves it in the form in which it is used: a linear relation among the
`D_m` holds for `ρ` at `4/3`.

* **The strip** (`stripR`, a definition; `isOpen_stripR`, `isPreconnected_stripR` and
  `im_hhat_ne_zero_of_mem`): `1 < Re s`, `0 < Im s < π/r`, open and convex, on which `Im ĥ(s) > 0` (round
  418's `im_hhat_pos`).
* **Round 430's identity along the strip** (`dirL` and `pairF`, definitions; `pairF_eq`,
  `differentiableOn_pairF` and **`tendsto_pairF`**): for `m = δ₃x` with `x ≠ 0` and `ψ = 1_{[1, 2]}`,
  `F_x(s) = ⟨P_m(ψ), ũ_s⟩ + ⟨P_m(ψ), E(1[Y ≤ v ≤ Y + 3]v^s)⟩` is `Λ_x(s)·J(s)`, with
  `Λ_x(s) = (2π/Γ(s))(2π|m|/9)^{s−1}·D_m(s)`, for `Re s > 2` on the strip (round 430's
  `inner_pmSer_uL_bessel`, the term `I_m·M_ψ(2 − s)` vanishing by round 435's `integral_fundP3_ebr_eq_zero`).
  `F_x` is complex-differentiable on the strip (round 424's `differentiableAt_uL`), and
  `iε·F_x(4/3 + iε) → ρ(x)·J(4/3)` as `ε → 0⁺` (round 425's `tendsto_uL_thetaL`).
* **Relations among the Dirichlet series** (**`sum_rhoM_eq_zero`**): for `x_i ≠ 0` and entire `a_i`, if
  `Σ_i a_i(s)·Λ_{x_i}(s) = 0` for `Re s > 2`, then `Σ_i a_i(4/3)·ρ(x_i) = 0`.
-/

open Ideal NumberField MeasureTheory Set Filter Topology Complex
open scoped BigOperators ComplexConjugate

noncomputable section

namespace Eis

/-! ### The strip -/

/-- The strip `1 < Re s`, `0 < Im s < π/r`. -/
def stripR (r : ℝ) : Set ℂ := {s | 1 < s.re ∧ 0 < s.im ∧ s.im < Real.pi / r}

/-- The strip is open. -/
theorem isOpen_stripR (r : ℝ) : IsOpen (stripR r) :=
  (isOpen_lt continuous_const Complex.continuous_re).inter
    ((isOpen_lt continuous_const Complex.continuous_im).inter
      (isOpen_lt Complex.continuous_im continuous_const))

/-- The strip is convex, so preconnected. -/
theorem isPreconnected_stripR (r : ℝ) : IsPreconnected (stripR r) := by
  have h : stripR r = {c : ℂ | 1 < c.re} ∩ ({c : ℂ | 0 < c.im} ∩ {c : ℂ | c.im < Real.pi / r}) := by
    ext s; simp [stripR]
  rw [h]
  exact ((convex_halfSpace_re_gt (r := 1)).inter ((convex_halfSpace_im_gt (r := 0)).inter
    (convex_halfSpace_im_lt (r := Real.pi / r)))).isPreconnected

/-- `Im ĥ(s) ≠ 0` on the strip (round 418's `im_hhat_pos`). -/
theorem im_hhat_ne_zero_of_mem {r : ℝ} (hr : 0 < r) {s : ℂ} (hs : s ∈ stripR r) :
    (hhat (2 * Real.cosh r - 2) s).im ≠ 0 :=
  (im_hhat_pos hr hs.1 hs.2.1 ((lt_div_iff₀ hr).1 hs.2.2)).ne'

/-! ### Round 430's identity along the strip -/

/-- Round 430's Dirichlet series at `m = δ₃x`, completed: `(2π/Γ(s))(2π|m|/9)^{s−1}·D_m(s)`. -/
def dirL (x : 𝓞 K) (s : ℂ) : ℂ :=
  2 * Real.pi / Gamma s * ((2 * Real.pi * ‖σO (δ3 * x) / 9‖ : ℝ) : ℂ) ^ (s - 1) *
    ∑' c : 𝓞 K, cuspSm (δ3 * x) c * ((Complex.normSq (σO c) : ℝ) : ℂ) ^ (-s)

/-- The pairing side of round 430's identity at `m = δ₃x`, with `ψ = 1_{[1, 2]}`:
`⟨P_m(ψ), ũ_s⟩ + ⟨P_m(ψ), E(1[Y ≤ v ≤ Y + 3]v^s)⟩`. -/
def pairF (x : 𝓞 K) (r Y : ℝ) (hY : 0 < Y) (s : ℂ) : ℂ :=
  inner ℂ ((memLp_pmSer_ind12 (δ3 * x)).toLp (pmSer (δ3 * x) ind12))
      (uL (2 * Real.cosh r - 2) (cosh_sub_nonneg r) Y hY s) +
    inner ℂ ((memLp_pmSer_ind12 (δ3 * x)).toLp (pmSer (δ3 * x) ind12))
      (bandL hY (le_band one_pos one_le_two) s)

/-- **Round 430's identity**, for `x ≠ 0`, `Re s > 2` and `Im ĥ(s) ≠ 0`: `F_x(s) = Λ_x(s)·J(s)`, the term
`I_m·M_ψ(2 − s)` vanishing since `I_m = 0` (round 435's `integral_fundP3_ebr_eq_zero`). -/
theorem pairF_eq {x : 𝓞 K} (hx : x ≠ 0) {r : ℝ} {Y : ℝ} (hY : 0 < Y) {s : ℂ} (hs : 2 < s.re)
    (him : (hhat (2 * Real.cosh r - 2) s).im ≠ 0) :
    pairF x r Y hY s = dirL x s * jPsi (4 * Real.pi * ‖σO (δ3 * x) / 9‖) ind12 s := by
  have h := inner_pmSer_uL_bessel hx (cosh_sub_nonneg r) hY measurable_ind12 (memLp_pmSer_ind12 (δ3 * x))
    norm_ind12_le (fun v hv => ind12_eq_zero hv) one_pos one_le_two hs him
  rw [integral_fundP3_ebr_eq_zero hx, zero_mul, add_zero] at h
  rw [pairF, h, dirL]
  ring

/-- `F_x` is complex-differentiable on the strip (round 424's `differentiableAt_uL`, round 430's
`differentiable_inner_bandL`). -/
theorem differentiableOn_pairF (x : 𝓞 K) {r : ℝ} (hr : 0 < r) {Y : ℝ} (hY : 0 < Y) :
    DifferentiableOn ℂ (pairF x r Y hY) (stripR r) := by
  intro s hs
  refine DifferentiableAt.differentiableWithinAt ?_
  unfold pairF
  exact (((innerSL ℂ _).differentiableAt).comp s
    (differentiableAt_uL hr.le hY (im_hhat_ne_zero_of_mem hr hs))).add (differentiable_inner_bandL _ hY _ s)

/-- **The residue of `F_x` at `4/3`**: `iε·F_x(4/3 + iε) → ρ(x)·J(4/3)` as `ε → 0⁺`, for `x ≠ 0` (round 425's
`tendsto_uL_thetaL`, and round 431's `rhoM`). -/
theorem tendsto_pairF {x : 𝓞 K} (hx : x ≠ 0) {r : ℝ} (hr : 0 < r) {Y : ℝ} (hY : 0 < Y) :
    Tendsto (fun ε : ℝ => (I * ε) * pairF x r Y hY (((4 / 3 : ℝ) : ℂ) + I * ε)) (𝓝[>] 0)
      (𝓝 (rhoM x r Y hY * jPsi (4 * Real.pi * ‖σO (δ3 * x) / 9‖) ind12 (4 / 3))) := by
  set P := (memLp_pmSer_ind12 (δ3 * x)).toLp (pmSer (δ3 * x) ind12) with hP
  have ha : 0 < 4 * Real.pi * ‖σO (δ3 * x) / 9‖ := by
    have h9 : σO (δ3 * x) / 9 ≠ 0 := div_ne_zero (σO_ne_zero (mul_ne_zero δ3_ne_zero hx)) (by norm_num)
    have := norm_pos_iff.2 h9
    positivity
  have hθ : inner ℂ P (thetaL r Y hY) =
      rhoM x r Y hY * jPsi (4 * Real.pi * ‖σO (δ3 * x) / 9‖) ind12 (4 / 3) := by
    rw [rhoM, div_mul_cancel₀ _ (jPsi_ind12_ne_zero ha)]
  have h1 : Tendsto (fun ε : ℝ => inner ℂ P ((I * ε) • uL (2 * Real.cosh r - 2) (cosh_sub_nonneg r) Y hY
      (((4 / 3 : ℝ) : ℂ) + I * ε))) (𝓝[>] 0) (𝓝 (inner ℂ P (thetaL r Y hY))) :=
    ((innerSL ℂ P).continuous.tendsto _).comp (tendsto_uL_thetaL hr hY)
  have hs : Tendsto (fun ε : ℝ => ((4 / 3 : ℝ) : ℂ) + I * ε) (𝓝[>] 0) (𝓝 (((4 / 3 : ℝ) : ℂ) + I * (0 : ℝ))) :=
    ((continuous_const.add (continuous_const.mul Complex.continuous_ofReal)).tendsto 0).mono_left
      nhdsWithin_le_nhds
  have hI : Tendsto (fun ε : ℝ => I * (ε : ℂ)) (𝓝[>] 0) (𝓝 (I * ((0 : ℝ) : ℂ))) :=
    ((continuous_const.mul Complex.continuous_ofReal).tendsto 0).mono_left nhdsWithin_le_nhds
  have h2 : Tendsto (fun ε : ℝ => (I * ε) * inner ℂ P (bandL hY (le_band one_pos one_le_two)
      (((4 / 3 : ℝ) : ℂ) + I * ε))) (𝓝[>] 0)
      (𝓝 ((I * ((0 : ℝ) : ℂ)) * inner ℂ P (bandL hY (le_band one_pos one_le_two)
        (((4 / 3 : ℝ) : ℂ) + I * (0 : ℝ))))) :=
    hI.mul (((differentiable_inner_bandL P hY (le_band one_pos one_le_two)).continuous.tendsto _).comp hs)
  have h3 := h1.add h2
  rw [Complex.ofReal_zero, mul_zero, zero_mul, add_zero, hθ] at h3
  refine h3.congr fun ε => ?_
  rw [pairF, ← hP, mul_add, inner_smul_right]

/-! ### Linear relations among the Dirichlet series -/

/-- **Relations among the `D_m` hold for `ρ` at `4/3`**: for `x_i ≠ 0` and entire `a_i`, if
`Σ_i a_i(s)·Λ_{x_i}(s) = 0` for `Re s > 2`, then `Σ_i a_i(4/3)·ρ(x_i) = 0`. The products
`F_{x_i}·Π_{j ≠ i}J_j` are complex-differentiable on the strip and their combination vanishes for `Re s > 2`
there, so on the whole strip (the identity theorem); `iε` times it at `4/3 + iε` tends to
`(Σ_i a_i(4/3)ρ(x_i))·Π_j J_j(4/3)`, and `J_j(4/3) ≠ 0` (round 431's `jPsi_ind12_ne_zero`). -/
theorem sum_rhoM_eq_zero {r : ℝ} (hr : 0 < r) {Y : ℝ} (hY : 0 < Y) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → 𝓞 K) (hx : ∀ i, x i ≠ 0) (a : ι → ℂ → ℂ) (ha : ∀ i, Differentiable ℂ (a i))
    (h : ∀ s : ℂ, 2 < s.re → ∑ i, a i s * dirL (x i) s = 0) :
    ∑ i, a i (4 / 3) * rhoM (x i) r Y hY = 0 := by
  set J : ι → ℂ → ℂ := fun i => jPsi (4 * Real.pi * ‖σO (δ3 * x i) / 9‖) ind12 with hJdef
  have hpos : ∀ i, 0 < 4 * Real.pi * ‖σO (δ3 * x i) / 9‖ := by
    intro i
    have h9 : σO (δ3 * x i) / 9 ≠ 0 := div_ne_zero (σO_ne_zero (mul_ne_zero δ3_ne_zero (hx i))) (by norm_num)
    have := norm_pos_iff.2 h9
    positivity
  have hJd : ∀ i, Differentiable ℂ (J i) := fun i =>
    differentiable_jPsi measurable_ind12 norm_ind12_le (fun v hv => ind12_eq_zero hv) one_pos (hpos i)
  have hJ0 : ∀ i, J i (4 / 3) ≠ 0 := fun i => jPsi_ind12_ne_zero (hpos i)
  set G : ℂ → ℂ := fun s => ∑ i, a i s * pairF (x i) r Y hY s * ∏ j ∈ Finset.univ.erase i, J j s with hG
  have hGd : DifferentiableOn ℂ G (stripR r) := by
    refine DifferentiableOn.fun_sum fun i _ => ?_
    refine (((ha i).differentiableOn).mul (differentiableOn_pairF (x i) hr hY)).mul ?_
    exact DifferentiableOn.fun_finsetProd fun j _ => (hJd j).differentiableOn
  set t : ℝ := Real.pi / (2 * r) with ht
  have ht0 : 0 < t := by positivity
  have ht1 : t < Real.pi / r := by
    rw [ht, div_lt_div_iff₀ (by positivity) hr]
    nlinarith [mul_pos Real.pi_pos hr]
  have hre : ((3 : ℂ) + I * (t : ℂ)).re = 3 := by simp
  have him : ((3 : ℂ) + I * (t : ℂ)).im = t := by simp
  have hz₀ : (3 : ℂ) + I * (t : ℂ) ∈ stripR r :=
    ⟨by rw [hre]; norm_num, by rw [him]; exact ht0, by rw [him]; exact ht1⟩
  have hev : G =ᶠ[𝓝 ((3 : ℂ) + I * (t : ℂ))] 0 := by
    have hU : {s : ℂ | 2 < s.re} ∩ stripR r ∈ 𝓝 ((3 : ℂ) + I * (t : ℂ)) :=
      ((isOpen_lt continuous_const Complex.continuous_re).inter (isOpen_stripR r)).mem_nhds
        ⟨show 2 < ((3 : ℂ) + I * (t : ℂ)).re by rw [hre]; norm_num, hz₀⟩
    filter_upwards [hU] with s hs
    have e : ∀ i, a i s * pairF (x i) r Y hY s * ∏ j ∈ Finset.univ.erase i, J j s =
        a i s * dirL (x i) s * ∏ j, J j s := by
      intro i
      rw [pairF_eq (hx i) hY hs.1 (im_hhat_ne_zero_of_mem hr hs.2),
        ← Finset.mul_prod_erase Finset.univ (fun j => J j s) (Finset.mem_univ i)]
      simp only [hJdef]
      ring
    simp only [hG, Pi.zero_apply]
    rw [Finset.sum_congr rfl fun i _ => e i, ← Finset.sum_mul, h s hs.1, zero_mul]
  have hzero := (hGd.analyticOnNhd (isOpen_stripR r)).eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (isPreconnected_stripR r) hz₀ hev
  have hs : Tendsto (fun ε : ℝ => ((4 / 3 : ℝ) : ℂ) + I * ε) (𝓝[>] 0) (𝓝 (4 / 3 : ℂ)) := by
    have h0 : Tendsto (fun ε : ℝ => ((4 / 3 : ℝ) : ℂ) + I * ε) (𝓝[>] 0)
        (𝓝 (((4 / 3 : ℝ) : ℂ) + I * ((0 : ℝ) : ℂ))) :=
      ((continuous_const.add (continuous_const.mul Complex.continuous_ofReal)).tendsto 0).mono_left
        nhdsWithin_le_nhds
    have e : ((4 / 3 : ℝ) : ℂ) + I * ((0 : ℝ) : ℂ) = 4 / 3 := by push_cast; ring
    rw [e] at h0
    exact h0
  have hlim : Tendsto (fun ε : ℝ => ∑ i, a i (((4 / 3 : ℝ) : ℂ) + I * ε) *
      ((I * ε) * pairF (x i) r Y hY (((4 / 3 : ℝ) : ℂ) + I * ε)) *
        ∏ j ∈ Finset.univ.erase i, J j (((4 / 3 : ℝ) : ℂ) + I * ε)) (𝓝[>] 0)
      (𝓝 (∑ i, a i (4 / 3) * (rhoM (x i) r Y hY * J i (4 / 3)) *
        ∏ j ∈ Finset.univ.erase i, J j (4 / 3))) := by
    refine tendsto_finsetSum _ fun i _ => ?_
    refine ((((ha i).continuous.tendsto _).comp hs).mul (tendsto_pairF (hx i) hr hY)).mul ?_
    exact tendsto_finsetProd _ fun j _ => ((hJd j).continuous.tendsto _).comp hs
  have hev0 : ∀ᶠ ε : ℝ in 𝓝[>] 0, (∑ i, a i (((4 / 3 : ℝ) : ℂ) + I * ε) *
      ((I * ε) * pairF (x i) r Y hY (((4 / 3 : ℝ) : ℂ) + I * ε)) *
        ∏ j ∈ Finset.univ.erase i, J j (((4 / 3 : ℝ) : ℂ) + I * ε)) = 0 := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < Real.pi / r by positivity)] with ε hε
    have hmem : ((4 / 3 : ℝ) : ℂ) + I * ε ∈ stripR r := by
      refine ⟨?_, ?_, ?_⟩ <;> simp only [add_re, add_im, mul_re, mul_im, I_re, I_im, ofReal_re, ofReal_im]
      · norm_num
      · simpa using hε.1
      · simpa using hε.2
    have hz := hzero hmem
    simp only [hG, Pi.zero_apply] at hz
    have e : ∑ i, a i (((4 / 3 : ℝ) : ℂ) + I * ε) *
        ((I * ε) * pairF (x i) r Y hY (((4 / 3 : ℝ) : ℂ) + I * ε)) *
        ∏ j ∈ Finset.univ.erase i, J j (((4 / 3 : ℝ) : ℂ) + I * ε) =
        (I * ε) * ∑ i, a i (((4 / 3 : ℝ) : ℂ) + I * ε) * pairF (x i) r Y hY (((4 / 3 : ℝ) : ℂ) + I * ε) *
          ∏ j ∈ Finset.univ.erase i, J j (((4 / 3 : ℝ) : ℂ) + I * ε) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [e, hz, mul_zero]
  have hL := tendsto_nhds_unique hlim (tendsto_const_nhds.congr' (hev0.mono fun ε hε => hε.symm))
  have e : ∑ i, a i (4 / 3) * (rhoM (x i) r Y hY * J i (4 / 3)) * ∏ j ∈ Finset.univ.erase i, J j (4 / 3) =
      (∑ i, a i (4 / 3) * rhoM (x i) r Y hY) * ∏ j, J j (4 / 3) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.mul_prod_erase Finset.univ (fun j => J j (4 / 3)) (Finset.mem_univ i)]
    ring
  rw [e] at hL
  exact (mul_eq_zero.1 hL).resolve_right (Finset.prod_ne_zero_iff.2 fun j _ => hJ0 j)

end Eis

end

#print axioms Eis.isOpen_stripR
#print axioms Eis.isPreconnected_stripR
#print axioms Eis.im_hhat_ne_zero_of_mem
#print axioms Eis.pairF_eq
#print axioms Eis.differentiableOn_pairF
#print axioms Eis.tendsto_pairF
#print axioms Eis.sum_rhoM_eq_zero
