import Mathlib
import WeilRH
import SimpleCont

/-! # The first positivity failure (round 161)

The in-house route to RH is a continuity argument in the support: `λ₁(a) > 0` at small `a`
(round 106), `λ₁` is continuous (round 147) and nonincreasing (round 46), so if Weil positivity ever
fails it fails *first* at a definite support `a₁`, where the form is still positive semidefinite
and has a normalised kernel vector. This file proves that structure theorem for `ζ`. Round 161
assumed Weil's criterion's finite-exception hypothesis; round 220 (`WeilLandau.rh_of_weil`) removed it.

* `lam_ge_quarter`: `λ₁(a) ≥ 1/4` for `0 < a ≤ 1/16` (pure Lean, no zero of `ζ`).
* `exists_lam_neg_of_not_RH`: `¬RH` gives a support with `λ₁ < 0`.
* `first_failure`: `¬RH` gives `a₁ > 1/16` with
  - `λ₁ > 0` on `(0, a₁)`, `λ₁(a₁) = 0`, `λ₁ ≤ 0` on `[a₁, ∞)`, `λ₁ < 0` somewhere;
  - `Q ≥ 0` on every probe at support `a₁` (the form is PSD there);
  - a normalised ground state `g*` with `Q(g*) = 0` and the **kernel equation**
    `B(g*, ψ) = bil0(g*, ψ) + 2·ĝ*(i/2)·ψ̂(i/2) = 0` for every probe `ψ`.

Contrapositive: RH follows from ruling out a normalised probe `g*` that is
simultaneously a zero of a PSD Weil form and in its kernel. That is a reformulation. It has no
bearing on RH.
-/

open Real Filter Topology Complex Set MeasureTheory

noncomputable section

namespace Pilot1ca

open Pilot1bt PilotWeil

/-- **`λ₁ ≥ 1/4` at small support**, from round 106's probe-wise bound. -/
theorem lam_ge_quarter {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1 / 16) : (1 / 4 : ℝ) ≤ lam a := by
  refine le_csInf ⟨_, box a, box_probe a, normSq_box ha, rfl⟩ ?_
  rintro q ⟨g, hp, hn, rfl⟩
  exact weilQ_ge_quarter ha ha1 hp hn

/-- The failure of RH gives a support with `λ₁ < 0`. -/
theorem exists_lam_neg_of_not_RH (hRH : ¬RiemannHypothesis) : ∃ a, 0 < a ∧ lam a < 0 := by
  have h := mt weil_criterion_zeta.1 hRH
  push Not at h
  obtain ⟨a, g, ha, hp, hq⟩ := h
  refine ⟨a, ha, ?_⟩
  by_contra hl
  push Not at hl
  have := lam_mul_le hp
  have := mul_nonneg hl (normSq_nonneg g)
  linarith

/-- **The first positivity failure.** If RH fails, there is a first support `a₁ > 1/16` at which Weil positivity is lost:
`λ₁` is positive before it, zero at it, nonpositive after it, and negative somewhere; the form is
positive semidefinite at `a₁`; and some normalised ground state `g*` is an exact null vector,
`Q(g*) = 0`, lying in the kernel of the bilinear form. -/
theorem first_failure (hRH : ¬RiemannHypothesis) :
    ∃ a₁, 1 / 16 < a₁ ∧ (∀ a, 0 < a → a < a₁ → 0 < lam a) ∧ lam a₁ = 0 ∧
      (∀ a, a₁ ≤ a → lam a ≤ 0) ∧ (∃ a₀, a₁ ≤ a₀ ∧ lam a₀ < 0) ∧
      (∀ ψ, Probe a₁ ψ → 0 ≤ weilQ a₁ ψ) ∧
      ∃ g, IsGroundState a₁ g ∧ weilQ a₁ g = 0 ∧
        ∀ ψ, Probe a₁ ψ → bil0 a₁ g ψ + 2 * poleR g a₁ * poleR ψ a₁ = 0 := by
  obtain ⟨a₀, ha₀, hl₀⟩ := exists_lam_neg_of_not_RH hRH
  set T : Set ℝ := {a | 0 < a ∧ lam a ≤ 0}
  have hT : T.Nonempty := ⟨a₀, ha₀, hl₀.le⟩
  have hTb : BddBelow T := ⟨0, fun _ h => h.1.le⟩
  set a₁ := sInf T
  -- every failing support exceeds `1/16`
  have hbig : ∀ a ∈ T, 1 / 16 < a := fun a h => by
    by_contra hc
    push Not at hc
    have := lam_ge_quarter h.1 hc
    linarith [h.2]
  have hge : 1 / 16 ≤ a₁ := le_csInf hT fun a h => (hbig a h).le
  have ha₁ : 0 < a₁ := by linarith
  -- before `a₁`: positive
  have hbefore : ∀ a, 0 < a → a < a₁ → 0 < lam a := fun a ha hlt => by
    by_contra hc
    push Not at hc
    exact absurd (csInf_le hTb ⟨ha, hc⟩) (not_le.2 hlt)
  -- after `a₁`: nonpositive
  have hafter : ∀ a, a₁ < a → lam a ≤ 0 := fun a hlt => by
    obtain ⟨b, hb, hba⟩ := exists_lt_of_csInf_lt hT hlt
    exact (lam_antitone hb.1 hba.le).trans hb.2
  -- continuity at `a₁`
  have hc : ContinuousAt lam a₁ := continuousOn_lam.continuousAt (Ioi_mem_nhds ha₁)
  have hle : lam a₁ ≤ 0 :=
    le_of_tendsto (x := 𝓝[>] a₁) (hc.tendsto.mono_left nhdsWithin_le_nhds)
      (eventually_nhdsWithin_of_forall fun a (h : a ∈ Ioi a₁) => hafter a h)
  have hge0 : 0 ≤ lam a₁ :=
    ge_of_tendsto (x := 𝓝[<] a₁) (hc.tendsto.mono_left nhdsWithin_le_nhds)
      (Filter.mem_of_superset (Ioo_mem_nhdsLT ha₁) fun a h => (hbefore a h.1 h.2).le)
  have hzero : lam a₁ = 0 := le_antisymm hle hge0
  have hstrict : 1 / 16 < a₁ := by
    rcases hge.lt_or_eq with h | h
    · exact h
    · have := lam_ge_quarter ha₁ h.symm.le
      linarith
  obtain ⟨g, hg⟩ := exists_groundState ha₁
  have hgq : weilQ a₁ g = 0 := (weilQ_eq_lam ha₁ hg).trans hzero
  refine ⟨a₁, hstrict, hbefore, hzero, fun a h => ?_, ⟨a₀, csInf_le hTb ⟨ha₀, hl₀.le⟩, hl₀⟩,
    fun ψ hψ => ?_, g, hg, hgq, fun ψ hψ => ?_⟩
  · rcases h.lt_or_eq with h | h
    · exact hafter a h
    · rw [← h]; exact hle
  · have := lam_mul_le hψ
    rw [hzero, zero_mul] at this
    exact this
  · have := euler_lagrange_mem ((isGroundState_iff ha₁).1 hg).1 hψ
    rw [hzero, zero_mul] at this
    exact this

end Pilot1ca

#print axioms Pilot1ca.lam_ge_quarter
#print axioms Pilot1ca.exists_lam_neg_of_not_RH
#print axioms Pilot1ca.first_failure
