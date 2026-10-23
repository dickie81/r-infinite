import KubotaThetaEq

/-! # The constant-term principle at `∞` (round 438)

S5f-11 of round 360's plan, part 1. Round 437's next step planned the constant-term principle through θ's
constant terms and pairings at the cusps of `Γ_1(3)`. This round proves it at `∞`, where it needs no other
cusp: θ (round 425's `thetaL`) lies in the closed span of the pseudo-Eisenstein series `E(ψ)` in `L²(ν)`,
`ν = ρ_G dμ` as in round 423, so θ is orthogonal to every automorphic function whose constant term at `∞`
vanishes. The results hold for every `r` and every `Y > 0`.

* **Eigenprojections and invariant subspaces** (**`starProjection_kerAt_mem`** and
  **`inner_starProjection_kerAt_eq_zero`**, with `orthogonal_invariant`): for `A` self-adjoint with `AS ⊆ S`,
  the orthogonal projection `P` onto the kernel of `A − l`, `l` real, maps `Sᗮ` into `Sᗮ`, so `⟨Px, f⟩ = 0`
  for `x ∈ S` and `f ∈ Sᗮ`.
* **Admissible profiles** (`PsAdm` and `bTransP`, definitions; **`psAdm_bTransP`**, **`ballOp_toLp_pseis`**
  and **`gL_mem_psSet`**, with `memLp_pseis_of_psAdm`, `bTransP_of_pos`, `bTrans_eq_zero` and
  `bavg_pseis_psAdm`): `ψ` measurable and bounded, vanishing outside `[α, β]` with `α > 0`. The ball transform
  of such a profile, set to `0` on `(−∞, 0]`, is one again, vanishing outside `[α/(R + 2), (R + 2)β]`, and the
  ball operator `K` sends `E(ψ)` to `E(Bψ)` (round 423's `bavg_pseis`, round 422's `ballOp_toLp_ae_eq_bavg`).
  Round 423's `g_s` is `E(ψ)` for an admissible `ψ` equal to `G_s` on `(0, ∞)`, for `Re s ≥ 0`.
* **θ in the closed span** (`psSet`, a definition; **`ballOp_mem_span_psSet`**,
  **`inner_thetaL_eq_zero_of_mem`**, **`inner_thetaL_eq_zero`** and **`thetaL_mem_closure`**): `K` preserves
  the span `S` of the `E(ψ)`, and `θ = −ĥ′(4/3)⁻¹·P g_{4/3}` with `g_{4/3} ∈ S`, so `θ ⊥ Sᗮ` and θ is in the
  closure of `S`.
* **The constant-term principle at `∞`** (**`inner_thetaL_eq_zero_of_const`**, with `enorm_slAct_of_isAut`):
  for `u` measurable, automorphic on `Γ_1(3)` with Kubota's character and in `L²(ν)`, with
  `∫_{3P} u(z, v) dz = 0` for almost every `v > 0`, `⟨θ, u⟩ = 0`, by round 426's unfolding and round 432's
  Fubini step.
-/

open MeasureTheory Set Filter NumberField Complex
open scoped ENNReal Topology MatrixGroups ComplexConjugate

noncomputable section

namespace Eis

/-! ### Eigenprojections and invariant subspaces -/

section Hilbert

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  {A : E →L[ℂ] E}

/-- **A self-adjoint operator preserving `S` preserves `Sᗮ`.** -/
theorem orthogonal_invariant (hA : IsSelfAdjoint A) {S : Submodule ℂ E} (hS : ∀ x ∈ S, A x ∈ S) :
    ∀ y ∈ Sᗮ, A y ∈ Sᗮ := by
  intro y hy
  rw [Submodule.mem_orthogonal] at hy ⊢
  intro u hu
  rw [← ContinuousLinearMap.adjoint_inner_left, hA.adjoint_eq]
  exact hy _ (hS u hu)

/-- **The eigenprojection preserves `Sᗮ`**: for `A` self-adjoint with `AS ⊆ S` and `l` real, the orthogonal
projection onto the kernel of `A − l` maps `Sᗮ` into `Sᗮ`. -/
theorem starProjection_kerAt_mem (hA : IsSelfAdjoint A) {S : Submodule ℂ E} (hS : ∀ x ∈ S, A x ∈ S)
    (l : ℝ) {f : E} (hf : f ∈ Sᗮ) : (kerAt A l).starProjection f ∈ Sᗮ := by
  set N := Sᗮ with hNdef
  have hN : ∀ y ∈ N, A y ∈ N := orthogonal_invariant hA hS
  have hN' : ∀ y ∈ Nᗮ, A y ∈ Nᗮ := orthogonal_invariant hA hN
  set B := A - algebraMap ℂ (E →L[ℂ] E) l with hBdef
  have hB : ∀ y, B y = A y - (l : ℂ) • y := fun y => by
    rw [hBdef, sub_apply, Algebra.algebraMap_eq_smul_one, smul_apply, one_apply_eq_self]
  set y := (kerAt A l).starProjection f with hydef
  have hy : B y = 0 := LinearMap.mem_ker.1 ((kerAt A l).starProjection_apply_mem f)
  set z := y - N.starProjection y with hzdef
  have hz : z ∈ Nᗮ := N.sub_starProjection_mem_orthogonal y
  have hBz : B z = 0 := by
    have h1 : B z ∈ Nᗮ := by
      rw [hB]
      exact Nᗮ.sub_mem (hN' z hz) (Nᗮ.smul_mem _ hz)
    have h2 : B z ∈ N := by
      have e : B z = -(B (N.starProjection y)) := by rw [hzdef, map_sub, hy, zero_sub]
      have hp := N.starProjection_apply_mem y
      rw [e, hB]
      exact N.neg_mem (N.sub_mem (hN _ hp) (N.smul_mem _ hp))
    have h3 : B z ∈ N ⊓ Nᗮ := ⟨h2, h1⟩
    rw [Submodule.inf_orthogonal_eq_bot] at h3
    exact (Submodule.mem_bot ℂ).1 h3
  have hzk : z ∈ kerAt A l := LinearMap.mem_ker.2 hBz
  have hzz : inner ℂ z z = 0 := by
    have e1 : inner ℂ (N.starProjection y) z = 0 :=
      Submodule.inner_right_of_mem_orthogonal (N.starProjection_apply_mem y) hz
    have e2 : inner ℂ y z = inner ℂ f z := by
      rw [hydef, Submodule.inner_starProjection_left_eq_right,
        (Submodule.starProjection_eq_self_iff (K := kerAt A l)).2 hzk]
    have e3 : inner ℂ f z = 0 := Submodule.inner_right_of_mem_orthogonal hf hz
    calc inner ℂ z z = inner ℂ y z - inner ℂ (N.starProjection y) z := inner_sub_left _ _ _
      _ = 0 := by rw [e1, e2, e3, sub_zero]
  have hz0 : z = 0 := inner_self_eq_zero.1 hzz
  have hyN : y = N.starProjection y := sub_eq_zero.1 hz0
  rw [hyN]
  exact N.starProjection_apply_mem y

/-- **The eigenprojection of a vector of `S` is orthogonal to `Sᗮ`**, for `A` self-adjoint with `AS ⊆ S`. -/
theorem inner_starProjection_kerAt_eq_zero (hA : IsSelfAdjoint A) {S : Submodule ℂ E}
    (hS : ∀ x ∈ S, A x ∈ S) (l : ℝ) {x : E} (hx : x ∈ S) {f : E} (hf : f ∈ Sᗮ) :
    inner ℂ ((kerAt A l).starProjection x) f = 0 := by
  rw [Submodule.inner_starProjection_left_eq_right]
  exact Submodule.inner_right_of_mem_orthogonal hx (starProjection_kerAt_mem hA hS l hf)

end Hilbert

/-! ### Admissible profiles -/

/-- **Admissible profiles**: measurable, bounded, and vanishing outside some `[α, β]` with `α > 0`. -/
def PsAdm (ψ : ℝ → ℂ) : Prop :=
  Measurable ψ ∧ ∃ M α β : ℝ, 0 < α ∧ (∀ v, ‖ψ v‖ ≤ M) ∧ ∀ v, v ∉ Icc α β → ψ v = 0

/-- `E(ψ)` is in `L²(ν)` for `ψ` admissible (round 427's `memLp_pseis_Icc`). -/
theorem memLp_pseis_of_psAdm {ψ : ℝ → ℂ} (h : PsAdm ψ) : MemLp (pseis ψ) 2 (muR rhoG) := by
  obtain ⟨hψ, M, α, β, hα, hM, hψ0⟩ := h
  exact memLp_pseis_Icc hψ hM hψ0 hα

/-- The ball transform, set to `0` on `(−∞, 0]`. -/
def bTransP (R : ℝ) (ψ : ℝ → ℂ) : ℝ → ℂ := (Ioi (0 : ℝ)).indicator (bTrans R ψ)

theorem bTransP_of_pos (R : ℝ) (ψ : ℝ → ℂ) {v : ℝ} (hv : 0 < v) : bTransP R ψ v = bTrans R ψ v :=
  indicator_of_mem (show v ∈ Ioi (0 : ℝ) from hv) _

/-- **A ball transform vanishes where the profile vanishes on the heights of the ball**: `Bψ(v) = 0` if
`ψ(w) = 0` for `v ≤ (R + 2)w` and `w ≤ (R + 2)v`. -/
theorem bTrans_eq_zero {R : ℝ} {ψ : ℝ → ℂ} {v : ℝ} (hv : 0 < v)
    (h : ∀ w, v ≤ (R + 2) * w → w ≤ (R + 2) * v → ψ w = 0) : bTrans R ψ v = 0 := by
  have hv' : ((0 : ℂ), v) ∈ UHS := hv
  unfold bTrans bavg
  have e : ∫ q in hball R (0, v), ψ q.2 ∂uhsMeasure = ∫ q in hball R (0, v), (0 : ℂ) ∂uhsMeasure :=
    setIntegral_congr_fun (measurableSet_hball R _) fun q hq =>
      h q.2 (le_snd_of_mem_hball hv' hq) (snd_le_of_mem_hball hv' hq)
  rw [e, integral_zero]

/-- **The ball transform of an admissible profile is admissible**, for `R ≥ 0`: bounded by `M·V_R`, and
vanishing outside `[α/(R + 2), (R + 2)β]`. -/
theorem psAdm_bTransP {R : ℝ} (hR : 0 ≤ R) {ψ : ℝ → ℂ} (h : PsAdm ψ) : PsAdm (bTransP R ψ) := by
  obtain ⟨hψ, M, α, β, hα, hM, hψ0⟩ := h
  have hR2 : 0 < R + 2 := by linarith
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  refine ⟨(measurable_bTrans R hψ).indicator measurableSet_Ioi, M * uhsMeasure.real (hball R (0, 1)),
    α / (R + 2), (R + 2) * β, div_pos hα hR2, fun v => ?_, fun v hv => ?_⟩
  · by_cases hv : 0 < v
    · rw [bTransP_of_pos R ψ hv]
      exact norm_bTrans_le_const hR (fun w _ => hM w) hv
    · rw [bTransP, indicator_of_notMem (show v ∉ Ioi (0 : ℝ) from hv), norm_zero]
      exact mul_nonneg hM0 measureReal_nonneg
  · by_cases hv0 : 0 < v
    · rw [bTransP_of_pos R ψ hv0]
      refine bTrans_eq_zero hv0 fun w h1 h2 => hψ0 w fun hw => hv ⟨?_, ?_⟩
      · rw [div_le_iff₀ hR2]
        linarith [hw.1]
      · nlinarith [hw.2]
    · rw [bTransP, indicator_of_notMem (show v ∉ Ioi (0 : ℝ) from hv0)]

/-- **`T_R E(ψ) = E(Bψ)`** on upper half-space, for `ψ` admissible and `R ≥ 0` (round 423's `bavg_pseis`). -/
theorem bavg_pseis_psAdm {R : ℝ} (hR : 0 ≤ R) {ψ : ℝ → ℂ} (h : PsAdm ψ) {p : ℂ × ℝ} (hp : p ∈ UHS) :
    bavg R (pseis ψ) p = pseis (bTransP R ψ) p := by
  obtain ⟨hψ, M, α, β, hα, hM, hψ0⟩ := h
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  rw [bavg_pseis hR hψ (by positivity : 0 ≤ M * (α ^ 3)⁻¹) (by norm_num : (2 : ℝ) < 3)
    (fun v hv => norm_le_pow_of_vanish hα hM0 (fun w _ hw => hψ0 w fun h => (not_le.2 hw) h.1)
      (fun w _ => hM w) hv) hp]
  exact pseis_congr (fun v hv => (bTransP_of_pos R ψ hv).symm) hp

/-- **The ball operator on `E(ψ)`**: `K E(ψ) = E(Bψ)` in `L²(ν)`, for `ψ` admissible and `R ≥ 0`. -/
theorem ballOp_toLp_pseis {R : ℝ} (hR : 0 ≤ R) {ψ : ℝ → ℂ} (h : PsAdm ψ) :
    ballOp isPU_rhoG isUChar_kub hR ((memLp_pseis_of_psAdm h).toLp (pseis ψ)) =
      (memLp_pseis_of_psAdm (psAdm_bTransP hR h)).toLp (pseis (bTransP R ψ)) := by
  refine Lp.ext ?_
  filter_upwards [ballOp_toLp_ae_eq_bavg isPU_rhoG isUChar_kub hR (isAut_pseis ψ) (measurable_pseis h.1)
      (memLp_pseis_of_psAdm h), (memLp_pseis_of_psAdm (psAdm_bTransP hR h)).coeFn_toLp,
    ae_muR_UHS rhoG] with p h1 h2 hp
  rw [h1, h2, bavg_pseis_psAdm hR h hp]

/-! ### θ in the closed span of the pseudo-Eisenstein series -/

/-- The pseudo-Eisenstein series of admissible profiles, in `L²(ν)`. -/
def psSet : Set (Lp ℂ 2 (muR rhoG)) :=
  {x | ∃ ψ : ℝ → ℂ, ∃ h : PsAdm ψ, x = (memLp_pseis_of_psAdm h).toLp (pseis ψ)}

/-- **The ball operator preserves the span of the `E(ψ)`**, for `R ≥ 0`. -/
theorem ballOp_mem_span_psSet {R : ℝ} (hR : 0 ≤ R) {x : Lp ℂ 2 (muR rhoG)}
    (hx : x ∈ Submodule.span ℂ psSet) :
    ballOp isPU_rhoG isUChar_kub hR x ∈ Submodule.span ℂ psSet := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨ψ, h, rfl⟩ := hy
      rw [ballOp_toLp_pseis hR h]
      exact Submodule.subset_span ⟨_, psAdm_bTransP hR h, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
  | smul a y _ hy => rw [map_smul]; exact Submodule.smul_mem _ a hy

/-- **`g_s` is a pseudo-Eisenstein series of an admissible profile**, for `R ≥ 0`, `Y > 0` and `Re s ≥ 0`:
`G_s` vanishes outside `[Y/(R + 2), (R + 2)Y]` on `(0, ∞)` (round 423's `gProf_eq_zero_of_lt` and
`gProf_eq_zero_of_ge`). -/
theorem gL_mem_psSet {R : ℝ} (hR : 0 ≤ R) {Y : ℝ} (hY : 0 < Y) {s : ℂ} (hs : 0 ≤ s.re) :
    gL R hR Y hY s ∈ psSet := by
  have hR2 : 0 < R + 2 := by linarith
  set ψ := (Ioi (0 : ℝ)).indicator (gProf R s Y) with hψ
  have h : PsAdm ψ := by
    refine ⟨(measurable_gProf R s Y).indicator measurableSet_Ioi,
      (uhsMeasure.real (hball R (0, 1)) + ‖hhat R s‖) * Y ^ s.re, Y / (R + 2), (R + 2) * Y,
      div_pos hY hR2, fun v => ?_, fun v hv => ?_⟩
    · by_cases hv : 0 < v
      · rw [hψ, indicator_of_mem (show v ∈ Ioi (0 : ℝ) from hv)]
        exact norm_gProf_le hR hs hY.le hv
      · rw [hψ, indicator_of_notMem (show v ∉ Ioi (0 : ℝ) from hv), norm_zero]
        exact mul_nonneg (add_nonneg measureReal_nonneg (norm_nonneg _)) (Real.rpow_nonneg hY.le _)
    · by_cases hv0 : 0 < v
      · rw [hψ, indicator_of_mem (show v ∈ Ioi (0 : ℝ) from hv0)]
        rcases not_and_or.1 hv with h1 | h1
        · exact gProf_eq_zero_of_lt hR s hv0 (shell_lt_of_lt_div hR (not_le.1 h1))
        · exact gProf_eq_zero_of_ge hR s hv0 (not_le.1 h1).le
      · rw [hψ, indicator_of_notMem (show v ∉ Ioi (0 : ℝ) from hv0)]
  refine ⟨ψ, h, ?_⟩
  refine MemLp.toLp_congr _ _ ?_
  filter_upwards [ae_muR_UHS rhoG] with p hp
  exact pseis_congr (fun v hv => (indicator_of_mem (show v ∈ Ioi (0 : ℝ) from hv) _).symm) hp

/-- **θ is orthogonal to `Sᗮ`**, `S` the span of the `E(ψ)`, for every `r` and `Y > 0`: `K` preserves `S`, and
`θ = −ĥ′(4/3)⁻¹·P g_{4/3}` with `g_{4/3} ∈ S`. -/
theorem inner_thetaL_eq_zero_of_mem (r : ℝ) {Y : ℝ} (hY : 0 < Y)
    {f : Lp ℂ 2 (muR rhoG)} (hf : f ∈ (Submodule.span ℂ psSet)ᗮ) : inner ℂ (thetaL r Y hY) f = 0 := by
  have hg : gL (2 * Real.cosh r - 2) (cosh_sub_nonneg r) Y hY ((4 / 3 : ℝ) : ℂ) ∈
      Submodule.span ℂ psSet :=
    Submodule.subset_span (gL_mem_psSet (cosh_sub_nonneg r) hY (by norm_num))
  rw [thetaL, inner_smul_left, inner_starProjection_kerAt_eq_zero
    (isSelfAdjoint_ballOp isPU_rhoG isUChar_kub (cosh_sub_nonneg r))
    (fun x hx => ballOp_mem_span_psSet (cosh_sub_nonneg r) hx) _ hg hf, mul_zero]

/-- **θ is orthogonal to every `f` orthogonal to the pseudo-Eisenstein series**: for every `r`, `Y > 0` and
`f ∈ L²(ν)` with `⟨E(ψ), f⟩ = 0` for every admissible `ψ`, `⟨θ, f⟩ = 0`. -/
theorem inner_thetaL_eq_zero (r : ℝ) {Y : ℝ} (hY : 0 < Y) {f : Lp ℂ 2 (muR rhoG)}
    (hf : ∀ ψ (h : PsAdm ψ), inner ℂ ((memLp_pseis_of_psAdm h).toLp (pseis ψ)) f = 0) :
    inner ℂ (thetaL r Y hY) f = 0 := by
  refine inner_thetaL_eq_zero_of_mem r hY ((Submodule.mem_orthogonal _ _).2 fun u hu => ?_)
  induction hu using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨ψ, h, rfl⟩ := hx
      exact hf ψ h
  | zero => exact inner_zero_left _
  | add x y _ _ hx hy => rw [inner_add_left, hx, hy, add_zero]
  | smul a x _ hx => rw [inner_smul_left, hx, mul_zero]

/-- **θ is in the closed span of the pseudo-Eisenstein series** of admissible profiles, for every `r` and
`Y > 0` (Mathlib's `Submodule.orthogonal_orthogonal_eq_closure`). -/
theorem thetaL_mem_closure (r : ℝ) {Y : ℝ} (hY : 0 < Y) :
    thetaL r Y hY ∈ (Submodule.span ℂ psSet).topologicalClosure := by
  rw [← Submodule.orthogonal_orthogonal_eq_closure, Submodule.mem_orthogonal']
  exact fun f hf => inner_thetaL_eq_zero_of_mem r hY hf

/-! ### The constant-term principle at `∞` -/

/-- `|u|` is invariant under `Γ_1(3)` for `u` automorphic with Kubota's character. -/
theorem enorm_slAct_of_isAut {u : ℂ × ℝ → ℂ} (hu : IsAut Gam3 (fun g => kub ↑g) u) :
    ∀ γ ∈ Gam3, ∀ p ∈ UHS, ‖u (slAct γ p)‖ₑ = ‖u p‖ₑ := by
  intro γ hγ p hp
  rw [hu γ hγ p hp, enorm_mul]
  have h1 : ‖kub (↑γ : Matrix (Fin 2) (Fin 2) (𝓞 K))‖ₑ = 1 := by
    rw [← ofReal_norm, isUChar_kub.norm_eq γ hγ, ENNReal.ofReal_one]
  rw [h1, one_mul]

/-- **The constant-term principle at `∞`**: for every `r`, `Y > 0`, and `u` measurable, automorphic on
`Γ_1(3)` with Kubota's character and in `L²(ν)`, whose constant term `∫_{3P} u(z, v) dz` vanishes for almost
every `v > 0`, `⟨θ, u⟩ = 0`. -/
theorem inner_thetaL_eq_zero_of_const (r : ℝ) {Y : ℝ} (hY : 0 < Y) {u : ℂ × ℝ → ℂ}
    (hum : Measurable u) (hu : IsAut Gam3 (fun g => kub ↑g) u) (hu2 : MemLp u 2 (muR rhoG))
    (h0 : ∀ᵐ v ∂(volume.restrict (Ioi (0 : ℝ))), ∫ z in fundP3, u (z, v) = 0) :
    inner ℂ (thetaL r Y hY) (hu2.toLp u) = 0 := by
  have hu1 : ∫⁻ p, ‖u p‖ₑ ∂(muR rhoG) < ⊤ := (hu2.integrable one_le_two).2
  refine inner_thetaL_eq_zero r hY fun ψ h => ?_
  obtain ⟨hψ, M, α, β, hα, hM, hψ0⟩ := id h
  have hT : MeasurableSet (fundP3 ×ˢ Icc α β) := measurableSet_fundP3.prod measurableSet_Icc
  have hbox : ∫⁻ p in fundP3 ×ˢ Icc α β, ‖u p‖ₑ ∂uhsMeasure < ⊤ :=
    (lintegral_mono_set (fun p hp => (⟨norm_le_six_of_mem_fundP3 hp.1, hp.2.1, hp.2.2⟩ :
      p ∈ boxZ 6 α β))).trans_lt (lintegral_boxZ_lt_top hum (enorm_slAct_of_isAut hu) hu1 6 hα β)
  have hui : IntegrableOn u (fundP3 ×ˢ Icc α β) := by
    refine ⟨hum.aestronglyMeasurable, ?_⟩
    show ∫⁻ p in fundP3 ×ˢ Icc α β, ‖u p‖ₑ < ⊤
    exact (setLIntegral_volume_le hum.enorm hT hα (fun p hp => ⟨hp.2.1, hp.2.2⟩)).trans_lt
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hbox)
  rw [inner_toLp_pseis hψ (memLp_pseis_of_psAdm h) hu hum hu2 (lintegral_rhoT3_ps_ne_top hM hψ0 hum hbox),
    integral_fundP3_conj_mul_of_int hψ hM hψ0 hα hum hui]
  refine integral_eq_zero_of_ae ?_
  filter_upwards [h0] with v hv
  simp only [hv, mul_zero, Pi.zero_apply]

end Eis

end

#print axioms Eis.orthogonal_invariant
#print axioms Eis.starProjection_kerAt_mem
#print axioms Eis.inner_starProjection_kerAt_eq_zero
#print axioms Eis.memLp_pseis_of_psAdm
#print axioms Eis.bTransP_of_pos
#print axioms Eis.bTrans_eq_zero
#print axioms Eis.psAdm_bTransP
#print axioms Eis.bavg_pseis_psAdm
#print axioms Eis.ballOp_toLp_pseis
#print axioms Eis.ballOp_mem_span_psSet
#print axioms Eis.gL_mem_psSet
#print axioms Eis.inner_thetaL_eq_zero_of_mem
#print axioms Eis.inner_thetaL_eq_zero
#print axioms Eis.thetaL_mem_closure
#print axioms Eis.enorm_slAct_of_isAut
#print axioms Eis.inner_thetaL_eq_zero_of_const
