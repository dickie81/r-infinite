import DHHadamard
import DirichletCharHalfPlane
import RealCharHalfPlane

/-! # Stack review 3, door D2′: the band `|2 Re ρ − 1| ≤ 5/6` for the zeros of every `L(s, χ)`, `χ ≠ 1`

D2 (`DoorRate.lean`) has the band for primitive real `χ`, through round 224's `LamG_one_sub`. The dh layer's
`LamG_one_sub'` (`Λ*(1 − s, χ) = ε_χ Λ*(s, χ⁻¹)` for every primitive `χ`) with round 495's half-plane at `χ⁻¹`
gives it for every primitive `χ ≠ 1`, and Mathlib's `LFunction_changeLevel` carries it to every `χ ≠ 1`. -/

open Complex DirichletCharacter

namespace StackReview3

variable {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}

/-- A zero of `L(s, χ)` in the critical strip, `χ` primitive, reflects to a zero of `L(1 − s, χ⁻¹)`. -/
theorem LFunction_inv_one_sub_eq_zero (hprim : χ.IsPrimitive) {s : ℂ}
    (hs : LFunction χ s = 0) (h0 : 0 < s.re) (h1 : s.re < 1) :
    LFunction χ⁻¹ (1 - s) = 0 := by
  by_contra hne
  have h1' : 0 < (1 - s).re := by simp; linarith
  have hL := PsiOmega.LamG_ne_zero h1' hne
  rw [PsiOmega.LamG_one_sub' (PsiOmega.isPrimitive_inv χ hprim), inv_inv] at hL
  apply hL
  have hz : PsiOmega.LamG χ s = 0 := by
    unfold PsiOmega.LamG
    rw [PsiOmega.completed_eq_mul h0, hs, mul_zero, mul_zero]
  rw [hz, mul_zero]

/-- **The band for every primitive `χ ≠ 1`**: round 495's half-plane at `χ` and at `χ⁻¹`. -/
theorem band_eleven_twelfths_of_isPrimitive (hχ : χ ≠ 1) (hprim : χ.IsPrimitive) {s : ℂ}
    (hs : LFunction χ s = 0) (h0 : 0 < s.re) (h1 : s.re < 1) :
    |2 * s.re - 1| ≤ 5 / 6 := by
  have hup : s.re ≤ 11 / 12 := by
    by_contra h
    exact Eis.LFunction_ne_zero_of_re_gt χ (lt_of_not_ge h) (Or.inl hχ) hs
  have hlow : (1 - s).re ≤ 11 / 12 := by
    by_contra h
    exact Eis.LFunction_ne_zero_of_re_gt χ⁻¹ (lt_of_not_ge h) (Or.inl (inv_ne_one.2 hχ))
      (LFunction_inv_one_sub_eq_zero hprim hs h0 h1)
  simp only [sub_re, one_re] at hlow
  rw [abs_le]
  constructor <;> linarith

/-- **The band for every `χ ≠ 1`**: in `0 < Re s`, a zero of `L(s, χ)` is a zero of `L(s, χ*)`, `χ*` primitive. -/
theorem band_eleven_twelfths_of_ne_one (hχ : χ ≠ 1) {s : ℂ}
    (hs : LFunction χ s = 0) (h0 : 0 < s.re) (h1 : s.re < 1) :
    |2 * s.re - 1| ≤ 5 / 6 := by
  have : NeZero χ.conductor := ⟨conductor_ne_zero χ⟩
  have hχ' : χ.primitiveCharacter ≠ 1 := by
    intro h
    apply hχ
    rw [← changeLevel_primitiveCharacter χ, h, changeLevel_one]
  have hfac := LFunction_changeLevel χ.conductor_dvd_level χ.primitiveCharacter (s := s) (Or.inl hχ')
  rw [changeLevel_primitiveCharacter, hs] at hfac
  have hprod : ∏ p ∈ N.primeFactors, (1 - χ.primitiveCharacter p * (p : ℂ) ^ (-s)) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro p hp
    exact Eis.RealChar.one_sub_mul_cpow_ne_zero (Nat.prime_of_mem_primeFactors hp) (norm_le_one _ _) h0
  have hL : LFunction χ.primitiveCharacter s = 0 := by
    rcases mul_eq_zero.1 hfac.symm with h | h
    · exact h
    · exact absurd h hprod
  exact band_eleven_twelfths_of_isPrimitive hχ' (primitiveCharacter_isPrimitive χ) hL h0 h1

end StackReview3

#print axioms StackReview3.band_eleven_twelfths_of_isPrimitive
#print axioms StackReview3.band_eleven_twelfths_of_ne_one
