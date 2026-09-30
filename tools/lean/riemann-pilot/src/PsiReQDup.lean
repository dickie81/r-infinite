import ArchShift

/-! # The duplication formula for `Re ψ` (round 247)

`psiReQ q + psiReQ (q + ½) = 2 psiReQ (2q)(2r) − 2 log 2`, Legendre's duplication for the digamma shift.
-/

open Real Complex

noncomputable section

namespace PsiReQDup

open Pilot1ca

theorem psiReQ_dup {q : ℝ} (hq : 0 < q) (r : ℝ) :
    psiReQ q r + psiReQ (q + 1 / 2) r = 2 * psiReQ (2 * q) (2 * r) - 2 * Real.log 2 := by
  unfold psiReQ
  have hs : ∀ m : ℕ, 2 * zQ q r ≠ -(m : ℂ) := by
    intro m h
    have := congrArg Complex.re h
    simp [zQ] at this
    nlinarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  have h := Complex.digamma_two_mul hs
  have e1 : zQ (2 * q) (2 * r) = 2 * zQ q r := by unfold zQ; push_cast; ring
  have e2 : zQ (q + 1 / 2) r = zQ q r + 1 / 2 := by unfold zQ; push_cast; ring
  rw [e1, e2, h]
  have hl : (Complex.log 2).re = Real.log 2 := by
    rw [Complex.log_re]; simp
  simp only [Complex.add_re, Complex.mul_re, hl]
  norm_num
  ring

end PsiReQDup

#print axioms PsiReQDup.psiReQ_dup
