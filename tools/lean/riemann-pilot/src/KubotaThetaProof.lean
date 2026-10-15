import KubotaCuspSeries
import KubotaRows

/-! # The Kubota–Patterson display, proved (round 466)

S5f-16 of round 360's plan. Round 465's next step planned round 361's display `KubotaTheta` from the clauses
rounds 436–465 prove for θ's Fourier series. This round assembles it, at `r = Y = 1`, and with round 381's
`ne_zero_of_kubotaTheta` the half-plane:

* **`KubotaTheta`** (**`kubotaTheta`**): the function is round 436's Fourier series `thS 1 1`, with constant
  term `phiG(4/3)/3` and coefficients `tauTh 1 1` at `∞` (round 436's `thS` and `dvd_of_tauTh_ne_zero`), and
  constant terms `0` and coefficients from round 465's `cusp_clauses` at `γ_±`. The constant `K` of the
  support and size condition is the larger of round 459's (`thetaSupp_tauTh`) and round 465's
  (`ThetaSupp.mono`). Invariance under `SL_2(ℤ)` is round 443's `atG_thS_int`, automorphy on `Γ_1(3)` round
  437's `atG_thS`, and the coefficient clause with `C ≠ 0` round 457's `exists_display_coef`.
* **The rows** (**`thetaRows`**): round 341's display `ThetaRows`, through round 381's `thetaRows_of_kubota`.
* **The route's other displays** (**`squarefreeCompleted`**, **`completedMeanSquare`**, **`dualMeanSquare`**
  and **`meanSquare`**): the companion paper's Lemma 6.6 (round 339's `SquarefreeCompleted`, through round
  342's `squarefreeCompleted_of` and round 359's `quadLargeSieve`), its Proposition 5.2 (round 314's
  `CompletedMeanSquare`, round 339), its (4.12) at every `ϑ > 0` (round 305's `DualMeanSquare`, round 315 with
  round 326's `transferEstimate`), and the family's mean square at every `σ > 0` (round 288's `MeanSquare`,
  round 310).
* **Every modulus** (round 493, step 2 of round 491's plan for door 5(b): **`thetaRowsM`**,
  **`squarefreeCompletedM`**, **`completedMeanSquareM`** and **`dualMeanSquareM`**): the displays of round 492 at
  every `md ≠ 0` (`ThetaRowsM md`, through round 493's `thetaRowsM_of_kubota`; `SquarefreeCompletedM md`;
  `CompletedMeanSquareM md`), and the dual mean square `DualMeanSquareM md ϑ` for the characters modulo every
  `md ≠ 0` with `4 ∣ md`, at every `ϑ > 0` (round 492's `dualMeanSquare_of_completed`).
* **The half-plane** (**`ne_zero_of_re_gt_eleven_twelfths`** and **`exists_zeroFree_halfPlane`**): `ζ(s) ≠ 0`
  and `L(s, χ₋₃) ≠ 0` for every `s` with `Re s > 11/12` (round 381's `ne_zero_of_kubotaTheta`), so there is
  `θ < 1` with `ζ(s) ≠ 0` on `Re s > θ`.
-/

open Complex NumberField Ideal
open scoped ComplexConjugate

noncomputable section

namespace Eis

/-- **Round 361's display `KubotaTheta`, proved**: θ's Fourier series at `r = Y = 1` (round 436's `thS`), with
the clauses at `∞` (rounds 436, 457 and 459), on `SL_2(ℤ)` (round 443) and `Γ_1(3)` (round 437), and at `γ_±`
(round 465). -/
theorem kubotaTheta : KubotaTheta := by
  obtain ⟨K₀, h₀⟩ := thetaSupp_tauTh (r := 1) one_pos (Y := 1) one_pos
  obtain ⟨K₁, tP, tM, hP, hM, hgP, hgM⟩ := cusp_clauses (r := 1) one_pos (Y := 1) one_pos
  obtain ⟨C, hC, hcoef⟩ := exists_display_coef (r := 1) one_pos (Y := 1) one_pos
  exact ⟨fun z v => thS 1 1 one_pos (z, v), max K₀ K₁, C, phiG (4 / 3) / 3, 0, 0, tauTh 1 1 one_pos, tP, tM,
    hC, h₀.mono (le_max_left _ _), hP.mono (le_max_right _ _), hM.mono (le_max_right _ _),
    fun _ h => dvd_of_tauTh_ne_zero h, fun _ _ _ => rfl, hgP, hgM,
    fun γ hdet z _ hv => atG_thS_int one_pos one_pos γ hdet z hv,
    fun γ hdet h3 z _ hv => atG_thS one_pos one_pos γ hdet h3 z hv, hcoef⟩

/-- **Round 341's display `ThetaRows`, proved** (round 381's `thetaRows_of_kubota`). -/
theorem thetaRows : ThetaRows := thetaRows_of_kubota kubotaTheta

/-- **The companion paper's Lemma 6.6, proved** (round 339's display `SquarefreeCompleted`): round 342's
`squarefreeCompleted_of` with `thetaRows` and round 359's `quadLargeSieve`. -/
theorem squarefreeCompleted : SquarefreeCompleted := squarefreeCompleted_of thetaRows quadLargeSieve

/-- **The companion paper's Proposition 5.2, proved** (round 314's display `CompletedMeanSquare`): round 339's
`completedMeanSquare_of_squarefree`. -/
theorem completedMeanSquare : CompletedMeanSquare := completedMeanSquare_of_squarefree squarefreeCompleted

/-- **The dual mean square at every `ϑ > 0`** (round 305's `DualMeanSquare`, the companion paper's (4.12)):
round 315's `dualMeanSquare_of_completed_transfer` with round 326's `transferEstimate`. -/
theorem dualMeanSquare {ϑ : ℝ} (hϑ : 0 < ϑ) : DualMeanSquare ϑ :=
  dualMeanSquare_of_completed_transfer completedMeanSquare transferEstimate hϑ

/-- **The family's mean square at every `σ > 0`** (round 288's `MeanSquare`): round 310's
`meanSquare_of_dualMeanSquare`. -/
theorem meanSquare {σ : ℝ} (hσ : 0 < σ) : MeanSquare σ := meanSquare_of_dualMeanSquare hσ (dualMeanSquare hσ)

/-- **Round 341's display at every modulus `md ≠ 0`** (`ThetaRowsM md`, round 493's
`thetaRowsM_of_kubota`). -/
theorem thetaRowsM {md : 𝓞 K} [NeZero md] : ThetaRowsM md := thetaRowsM_of_kubota kubotaTheta

/-- **The companion paper's Lemma 6.6 at every modulus `md ≠ 0`** (`SquarefreeCompletedM md`): round 342's
`squarefreeCompletedM_of` with `thetaRowsM` and round 359's `quadLargeSieve`. -/
theorem squarefreeCompletedM {md : 𝓞 K} [NeZero md] : SquarefreeCompletedM md :=
  squarefreeCompletedM_of thetaRowsM quadLargeSieve

/-- **The companion paper's Proposition 5.2 at every modulus `md ≠ 0`** (`CompletedMeanSquareM md`): round
339's `completedMeanSquareM_of_squarefree`. -/
theorem completedMeanSquareM {md : 𝓞 K} [NeZero md] : CompletedMeanSquareM md :=
  completedMeanSquareM_of_squarefree squarefreeCompletedM

/-- **The dual mean square for the characters modulo every `md ≠ 0` with `4 ∣ md`, at every `ϑ > 0`**
(`DualMeanSquareM md ϑ`, the companion paper's (4.12) at `md`): round 492's `dualMeanSquare_of_completed`. -/
theorem dualMeanSquareM {md : 𝓞 K} [NeZero md] [Fact ((4 : 𝓞 K) ∣ md)] {ϑ : ℝ} (hϑ : 0 < ϑ) :
    DualMeanSquareM md ϑ :=
  dualMeanSquare_of_completed completedMeanSquareM hϑ

/-- **The half-plane**: `ζ(s) ≠ 0` and `L(s, χ₋₃) ≠ 0` for `Re s > 11/12` (round 381's
`ne_zero_of_kubotaTheta`). -/
theorem ne_zero_of_re_gt_eleven_twelfths {s : ℂ} (hs : 11 / 12 < s.re) :
    riemannZeta s ≠ 0 ∧ DirichletCharacter.LFunction PsiOmega.chi3 s ≠ 0 :=
  ne_zero_of_kubotaTheta kubotaTheta hs

/-- **A zero-free half-plane for `ζ`**: there is `θ < 1` with `ζ(s) ≠ 0` for every `s` with `Re s > θ`
(`θ = 11/12`). -/
theorem exists_zeroFree_halfPlane : ∃ θ : ℝ, θ < 1 ∧ ∀ s : ℂ, θ < s.re → riemannZeta s ≠ 0 :=
  ⟨11 / 12, by norm_num, fun _ hs => (ne_zero_of_re_gt_eleven_twelfths hs).1⟩

end Eis

end


#print axioms Eis.kubotaTheta
#print axioms Eis.thetaRows
#print axioms Eis.squarefreeCompleted
#print axioms Eis.completedMeanSquare
#print axioms Eis.dualMeanSquare
#print axioms Eis.meanSquare
#print axioms Eis.thetaRowsM
#print axioms Eis.squarefreeCompletedM
#print axioms Eis.completedMeanSquareM
#print axioms Eis.dualMeanSquareM
#print axioms Eis.ne_zero_of_re_gt_eleven_twelfths
#print axioms Eis.exists_zeroFree_halfPlane
