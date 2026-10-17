import Mathlib
import WeilChiCriterion
import ArchShift

/-! # `Q_χ` in u-space (round 226)

`QC χ a g` (WeilChiCriterion.lean) is Weil's form for `L(s, χ)` in its Guinand–Weil presentation, with
`h = ĝ²` on the spectral side. For every probe it equals the u-space form that
`frontier/dh/dh_gram.py` computes:

  `Q_χ(g) = (Re ψ(q_χ) + log(N/π))‖g‖² + ∫_0^∞ [f(0) − f(u)] e^{(1−2q_χ)u}/sinh u du
            − 2Σ Λ(n)χ(n)n^{−1/2} f(log n)`   (`QC_eq_QCu`),

with `f = autocorr g` and `q_χ = (1 + 2δ)/4`: `¼` for even `χ` (ζ's kernel `e^{u/2}/sinh u`), `¾` for
odd `χ` (kernel `e^{−u/2}/sinh u`). The three instances `χ₋₃`, `χ₋₄`, `χ₋₈` are odd.

The proof is `gh_hsq` (Fourier inversion, `g_h = f`) for the constant and prime terms and
ArchShift.lean's `arch_termQ` for the archimedean term. No zero of `L` and no GoodChar hypothesis enter.
-/

open Real Complex MeasureTheory Set

noncomputable section

namespace PsiOmega

open DirichletCharacter Pilot1ca Pilot1bt

variable {N : ℕ} {χ : DirichletCharacter ℂ N} {a : ℝ} {g : ℝ → ℝ}

/-- The digamma shift `q_χ = (1 + 2δ)/4`. -/
def qC (χ : DirichletCharacter ℂ N) : ℝ := (1 + 2 * parity χ) / 4

theorem quarter_le_qC : 1 / 4 ≤ qC χ := by
  unfold qC; linarith [parity_nonneg' χ]

theorem qC_of_even (h : χ.Even) : qC χ = 1 / 4 := by
  classical
  unfold qC parity; simp only [h, ↓reduceIte]; norm_num

theorem qC_of_odd (h : χ.Odd) : qC χ = 3 / 4 := by
  classical
  have hne : ¬χ.Even := fun he => by
    have e : (1 : ℂ) = -1 := he.symm.trans h
    norm_num at e
  unfold qC parity; simp only [hne, ↓reduceIte]; norm_num

/-- `z_χ(r) = q_χ + ir/2`. -/
theorem psiReC_eq : psiReC χ = psiReQ (qC χ) := by
  funext r; unfold psiReC psiReQ zC zQ qC; congr 2; push_cast; ring

/-- **Weil's form for `L(s, χ)` in u-space**, as `dh_gram.py` computes it. -/
def QCu [NeZero N] (χ : DirichletCharacter ℂ N) (g : ℝ → ℝ) : ℝ :=
  ((Complex.digamma (qC χ)).re + Real.log N - Real.log π) * normSq g + archEQ (qC χ) g
    - 2 * ∑' n : ℕ, fχ χ n / Real.sqrt n * autocorr g (Real.log n)

/-- **The u-space bridge for `χ`**: for every probe, `Q_χ(g) = Q_χ^u(g)`. -/
theorem QC_eq_QCu [NeZero N] (hp : Probe a g) (ha : 0 < a) : QC χ a g = QCu χ g := by
  unfold QC QCu weilRHSC
  rw [psiReC_eq, arch_termQ hp ha quarter_le_qC, psiReQ_zero]
  simp only [gh_hsq hp.toE ha, autocorr_zero]
  ring

/-- For odd `χ` the archimedean kernel is `e^{−u/2}/sinh u`. -/
theorem archKer_odd (h : χ.Odd) (u : ℝ) : archKer (qC χ) u = Real.exp (-(u / 2)) / Real.sinh u := by
  rw [qC_of_odd h]; unfold archKer; congr 2; ring

/-- For even `χ` the archimedean term is ζ's. -/
theorem archEQ_even (h : χ.Even) : archEQ (qC χ) g = archE g := by
  rw [qC_of_even h, archEQ_quarter]

/-! ## The instances are odd -/

theorem chi3_odd : chi3.Odd := by
  show chi3 (-1) = -1
  rw [show (-1 : ZMod 3) = ((2 : ℕ) : ZMod 3) by decide, chi3_nat, χ₃_nat]; norm_num

theorem chi4_odd : chi4.Odd := by
  show chi4 (-1) = -1
  rw [show (-1 : ZMod 4) = ((3 : ℕ) : ZMod 4) by decide, chi4_nat,
    ZMod.χ₄_nat_three_mod_four (by norm_num)]; norm_num

theorem chi8_odd : chi8.Odd := by
  show chi8 (-1) = -1
  rw [show (-1 : ZMod 8) = ((7 : ℕ) : ZMod 8) by decide, chi8_nat,
    ZMod.χ₈'_nat_eq_if_mod_eight]; norm_num

end PsiOmega

#print axioms PsiOmega.QC_eq_QCu
#print axioms PsiOmega.archKer_odd
#print axioms PsiOmega.archEQ_even
#print axioms PsiOmega.chi3_odd
#print axioms PsiOmega.chi4_odd
#print axioms PsiOmega.chi8_odd
