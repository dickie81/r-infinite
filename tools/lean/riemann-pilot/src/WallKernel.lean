import ArchShift
import FourierGap
import SixteenPi

/-! # The wall law under the involution `X ↦ 4/X`, and the `Γ_ℂ` kernel (round 247)

`fBalExp X = 8π·w(4/X)`, so `SixteenPi`'s reduced exponent is the wall law at `4/X` and is maximal exactly at the wall `X = 2` (`fBalExp_le'`); `archKer ¼ − archKer ¾ = 1/cosh(u/2)` and `kerK` as the `Γ_ℂ` kernel plus a `cosh` correction.
-/

open Real

noncomputable section

namespace BalWall

open Pilot1ca

/-- The wall law `w(X) = (1 + log(X/2))/X`. -/
def w (X : ℝ) : ℝ := (1 + Real.log (X / 2)) / X

theorem fBalExp_eq_wall {X : ℝ} (hX : 0 < X) : fBalExp X = 8 * π * w (4 / X) := by
  unfold fBalExp w
  have h1 : (4 / X) / 2 = 2 / X := by field_simp; ring
  rw [h1, Real.log_div two_ne_zero hX.ne']
  field_simp
  ring

/-- `fBalExp_le` re-derived from `wall_le` and `wall_eq_iff`. -/
theorem fBalExp_le' {X : ℝ} (hX : 0 < X) : fBalExp X ≤ 4 * π ∧ (fBalExp X = 4 * π ↔ X = 2) := by
  have h4 : 0 < 4 / X := by positivity
  rw [fBalExp_eq_wall hX]
  have hw := wall_le h4
  have hwe := wall_eq_iff h4
  unfold w
  refine ⟨by nlinarith [pi_pos], ⟨fun h => ?_, fun h => ?_⟩⟩
  · have : (1 + Real.log (4 / X / 2)) / (4 / X) = 1 / 2 := by
      have := pi_pos
      field_simp at h ⊢
      nlinarith
    have := hwe.1 this
    field_simp at this
    linarith
  · subst h
    have := hwe.2 (by norm_num)
    rw [this]; ring

end BalWall

namespace ArchKerGammaC

open Pilot1ca

theorem archKer_quarter_sub {u : ℝ} (hu : 0 < u) :
    archKer (1 / 4) u - archKer (3 / 4) u = 1 / Real.cosh (u / 2) := by
  unfold archKer
  have hs : Real.sinh u = 2 * Real.sinh (u / 2) * Real.cosh (u / 2) := by
    have := Real.sinh_two_mul (u / 2)
    rwa [show 2 * (u / 2) = u by ring] at this
  have h2 : 0 < Real.sinh (u / 2) := Real.sinh_pos_iff.2 (by linarith)
  have hc : 0 < Real.cosh (u / 2) := Real.cosh_pos _
  rw [show (1 - 2 * (1 / 4 : ℝ)) * u = u / 2 by ring, show (1 - 2 * (3 / 4 : ℝ)) * u = -(u / 2) by ring,
    ← sub_div]
  have hsinh : Real.exp (u / 2) - Real.exp (-(u / 2)) = 2 * Real.sinh (u / 2) := by
    rw [Real.sinh_eq]; ring
  rw [hsinh, hs, div_eq_div_iff (mul_pos (mul_pos two_pos h2) hc).ne' hc.ne']
  ring

/-- **The odd-character kernel**, the twin of FourierGap's `kerK_eq`:
`K_{3/4}(u) = ½csch(u/2) − ½sech(u/2)`. -/
theorem archKer_three_quarter_eq {u : ℝ} (hu : 0 < u) :
    archKer (3 / 4) u = 1 / 2 / Real.sinh (u / 2) - 1 / 2 / Real.cosh (u / 2) := by
  have h1 := archKer_quarter_sub hu
  have h2 : archKer (1 / 4) u = kerK u := by
    unfold kerK archKer; rw [show (1 - 2 * (1 / 4 : ℝ)) * u = u / 2 by ring]
  rw [h2, kerK_eq hu] at h1
  have e : 1 / Real.cosh (u / 2) = 2 * (1 / 2 / Real.cosh (u / 2)) := by ring
  linarith

/-- **FourierGap's split, read through the Γ-factors**: `K = ½K_{1/2}(u/2) + ½sech(u/2)`, where
`K_{1/2}(u/2) = 1/sinh(u/2) = K_{1/4}(u) + K_{3/4}(u)` is the `Γ_ℂ` kernel. -/
theorem kerK_eq_gammaC {u : ℝ} (hu : 0 < u) :
    kerK u = archKer (1 / 2) (u / 2) / 2 + 1 / 2 / Real.cosh (u / 2) := by
  rw [kerK_eq hu]
  unfold archKer
  rw [show (1 - 2 * (1 / 2 : ℝ)) * (u / 2) = 0 by ring, Real.exp_zero]
  ring

end ArchKerGammaC

#print axioms BalWall.fBalExp_eq_wall
#print axioms BalWall.fBalExp_le'
#print axioms ArchKerGammaC.archKer_quarter_sub
#print axioms ArchKerGammaC.archKer_three_quarter_eq
#print axioms ArchKerGammaC.kerK_eq_gammaC
