import Mathlib
import KaiserPrefactor
import FirstFailure

/-! # Connes' prefactor `e^{9a}`, with an ineffective constant (round 220)

Round 164's `lam_prefactor` bounds `λ₁(a) ≤ K(a+1)e^{10a − 4πe^{2a}}`. The extra `e^a` over Connes'
`e^{9a}` is the weight `κ = e^{2a|Im τ|} ≤ e^a` of the off-line zeros (`lam_le_kappa`). README
round 164 named the clean way to remove it, a case split on RH, blocked only by the converse of
Weil's criterion for infinitely many off-line zeros. Round 220 proves that converse
(`WeilLandau.rh_of_weil`, via Landau's theorem), so the case split goes through:

* **RH holds.** Every `τ` is real (`tau_im_eq_zero_of_RH`), so `κ = 1` in `lam_le_kappa`.
* **RH fails.** Then `λ₁(a₀) < 0` at some support `a₀` (`exists_lam_neg_of_not_RH`), and `λ₁` is
  non-increasing (`lam_antitone`), so `λ₁ < 0` from `a₀` on. The range `[4, a₀]` is absorbed into the
  constant: `e^{10a} ≤ e^{a₀}e^{9a}` there.

`lam_nine`: `λ₁(a) ≤ K(a+1)e^{9a − 4πe^{2a}}` for every `a ≥ 4`. The constant `K` is ineffective: in
the second case it depends on the unknown `a₀`.

It is an upper bound on `λ₁`, compatible with RH and with its failure: no bearing on RH.
-/

open Complex Filter Topology MeasureTheory Real Set

noncomputable section

namespace Kaiser

open Pilot1ca Pilot1bt

/-- **Under RH every zero `τ` of `Ξ` is real.** -/
theorem tau_im_eq_zero_of_RH (hRH : RiemannHypothesis) (i : ZeroIdx (sqF Xi)) : (tau i).im = 0 := by
  set s : ℂ := 1 / 2 + I * tau i
  have hs : IsNontrivialZero s := by
    rw [nontrivial_iff_Xi]
    have e : (s - 1 / 2) / I = tau i := by simp only [s]; field_simp; ring
    rw [e]; exact Xi_tau i
  have h1 : s ≠ 1 := fun h => by
    have := hs.re_lt_one; rw [h, one_re] at this; exact lt_irrefl _ this
  have hre := hRH s hs.1 hs.2 h1
  have e : s.re = 1 / 2 - (tau i).im := by simp only [s]; simp; ring
  linarith

/-- **Connes' prefactor `e^{9a}`, ineffective constant.** `λ₁(a) ≤ K(a+1)e^{9a − 4πe^{2a}}` for every
`a ≥ 4`, by a case split on RH. -/
theorem lam_nine :
    ∃ K, 0 ≤ K ∧ ∀ a, 4 ≤ a → lam a ≤ K * (a + 1) * Real.exp (9 * a - 4 * π * Real.exp (2 * a)) := by
  by_cases hRH : RiemannHypothesis
  · obtain ⟨K, hK, h⟩ := lam_le_kappa
    refine ⟨K, hK, fun a ha => ?_⟩
    have := h a ha 1 zero_le_one fun i => by rw [tau_im_eq_zero_of_RH hRH i]; simp
    simpa using this
  · obtain ⟨a₀, ha₀, hl₀⟩ := exists_lam_neg_of_not_RH hRH
    obtain ⟨K, hK, h⟩ := lam_prefactor
    refine ⟨K * Real.exp a₀, by positivity, fun a ha => ?_⟩
    have hE : 0 ≤ Real.exp (9 * a - 4 * π * Real.exp (2 * a)) := (Real.exp_pos _).le
    rcases le_or_gt a a₀ with haa | haa
    · have hexp : Real.exp a ≤ Real.exp a₀ := Real.exp_le_exp.2 haa
      have h0 : 0 ≤ K * (a + 1) := mul_nonneg hK (by linarith)
      calc lam a ≤ K * (a + 1) * Real.exp (10 * a - 4 * π * Real.exp (2 * a)) := h a ha
        _ = K * (a + 1) * Real.exp a * Real.exp (9 * a - 4 * π * Real.exp (2 * a)) := by
            rw [mul_assoc (K * (a + 1)), ← Real.exp_add]; ring_nf
        _ ≤ K * (a + 1) * Real.exp a₀ * Real.exp (9 * a - 4 * π * Real.exp (2 * a)) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp h0) hE
        _ = _ := by ring
    · have := lam_antitone ha₀ haa.le
      have h0 : 0 ≤ K * Real.exp a₀ * (a + 1) * Real.exp (9 * a - 4 * π * Real.exp (2 * a)) :=
        mul_nonneg (mul_nonneg (by positivity) (by linarith)) hE
      linarith

end Kaiser

#print axioms Kaiser.tau_im_eq_zero_of_RH
#print axioms Kaiser.lam_nine
