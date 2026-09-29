import Mathlib
import WeilRH

/-! # Negative directions of `Q` count off-line zeros of ζ, with no named input (round 229)

Round 130's `finrank_le_quadruples` and `finrank_le_offline` (ExplicitBridge.lean) take Weil's explicit
formula for every probe of the space `V` as a hypothesis (`hEF`). Round 156 proved the formula over the
zeros of `riemannZeta` for every probe whose `ĝ²` is a strip test function (`weilExplicit_zeta`), and
round 157 for every `C²` probe vanishing near the edges (`weilExplicit_C2_zeta`). Here `hEF` is
discharged for ζ:

* `finrank_le_quadruples_zeta`, `finrank_le_offline_zeta`: if `Q` is negative definite on a
  finite-dimensional space `V` of strip-test probes, ζ has at least `dim V` distinct off-line zero
  quadruples (resp. off-line zeros outside any finite set `F` that holds them all number at least
  `dim V`).
* `finrank_le_quadruples_C2`: the same for `V` made of `C²` probes vanishing near `±a`.
* `exists_offline_of_neg_zeta`, `exists_offline_of_neg_C2`: one strip-test (or `C²`) probe with
  `Q < 0` exhibits an off-line zero.

So a certified negative-definite block of Weil's form, for instance from a Gram matrix of `C²` probes
in ball arithmetic, is a Lean-checkable lower bound on the number of off-line zeros.

Every scan so far finds `Q ≥ 0`. No bearing on RH: these are the counting half of Weil's criterion.
-/

open Real Complex MeasureTheory

noncomputable section

namespace Pilot1ca

open Pilot1bt PilotWeil

variable {a : ℝ}

/-- Weil's explicit formula over ζ's zeros for a probe whose `ĝ²` is a strip test function. -/
theorem weilExplicit_of_strip (ha : 0 < a) {g : ℝ → ℝ} (hp : Probe a g) {K : ℝ}
    (hK : StripTest (fun z => ghatC g a z ^ 2) K) :
    WeilExplicit zetaZeroFamily (fun z => ghatC g a z ^ 2) (hsq g a) :=
  weilExplicit_zeta hK (fun t => even_ghat_sq hp.even a t) (hsq_ofReal hp ha.le)

/-- `C²` probes vanishing near `±a` are strip-test probes. -/
theorem strip_of_C2 (ha : 0 < a) {g : ℝ → ℝ} (hp : Probe a g)
    (hc : ∃ r g₁ g₂, C2Supp r g g₁ g₂ ∧ 0 ≤ r ∧ r ≤ a) :
    ∃ K, StripTest (fun z => ghatC g a z ^ 2) K := by
  obtain ⟨r, g₁, g₂, hc, hr, hra⟩ := hc
  exact striptest_C2 ha hp hc hr hra

/-- **Negative directions are at most the off-line quadruples of ζ**, with no named input. `R` holds one
representative per off-line quadruple: every zero is on the line or has its ordinate in the orbit
`{t_r, −t_r, t̄_r, −t̄_r}` of some `r ∈ R`. -/
theorem finrank_le_quadruples_zeta (V : Submodule ℝ (ℝ → ℝ)) [FiniteDimensional ℝ V] (ha : 0 < a)
    (hV : ∀ v ∈ V, Probe a v) (hS : ∀ v ∈ V, ∃ K, StripTest (fun z => ghatC v a z ^ 2) K)
    (hneg : ∀ v ∈ V, v ≠ 0 → weilQ a v < 0)
    (R : Finset (Σ w : NontrivialZero, Fin (zeroMult w)))
    (hR : ∀ i, (zetaZeroFamily i).re = 1 / 2 ∨ ∃ r ∈ R,
      let t := (zetaZeroFamily i - 1 / 2) / Complex.I
      let w := (zetaZeroFamily r - 1 / 2) / Complex.I
      t = w ∨ t = -w ∨ t = (starRingEnd ℂ) w ∨ t = -(starRingEnd ℂ) w) :
    Module.finrank ℝ V ≤ R.card :=
  finrank_le_quadruples V ha hV hneg (fun v hv => by
    obtain ⟨K, hK⟩ := hS v hv; exact weilExplicit_of_strip ha (hV v hv) hK) R hR

/-- **The crude count**: if every zero of ζ outside the finite set `F` of indices is on the line and
`Q` is negative definite on a space `V` of strip-test probes, then `dim V ≤ |F|`. -/
theorem finrank_le_offline_zeta (V : Submodule ℝ (ℝ → ℝ)) [FiniteDimensional ℝ V] (ha : 0 < a)
    (hV : ∀ v ∈ V, Probe a v) (hS : ∀ v ∈ V, ∃ K, StripTest (fun z => ghatC v a z ^ 2) K)
    (hneg : ∀ v ∈ V, v ≠ 0 → weilQ a v < 0)
    (F : Finset (Σ w : NontrivialZero, Fin (zeroMult w)))
    (hF : ∀ i ∉ F, (zetaZeroFamily i).re = 1 / 2) :
    Module.finrank ℝ V ≤ F.card :=
  finrank_le_offline V ha hV hneg (fun v hv => by
    obtain ⟨K, hK⟩ := hS v hv; exact weilExplicit_of_strip ha (hV v hv) hK) F hF

/-- **The same for a space of `C²` probes vanishing near `±a`.** -/
theorem finrank_le_quadruples_C2 (V : Submodule ℝ (ℝ → ℝ)) [FiniteDimensional ℝ V] (ha : 0 < a)
    (hV : ∀ v ∈ V, Probe a v) (hc : ∀ v ∈ V, ∃ r v₁ v₂, C2Supp r v v₁ v₂ ∧ 0 ≤ r ∧ r ≤ a)
    (hneg : ∀ v ∈ V, v ≠ 0 → weilQ a v < 0)
    (R : Finset (Σ w : NontrivialZero, Fin (zeroMult w)))
    (hR : ∀ i, (zetaZeroFamily i).re = 1 / 2 ∨ ∃ r ∈ R,
      let t := (zetaZeroFamily i - 1 / 2) / Complex.I
      let w := (zetaZeroFamily r - 1 / 2) / Complex.I
      t = w ∨ t = -w ∨ t = (starRingEnd ℂ) w ∨ t = -(starRingEnd ℂ) w) :
    Module.finrank ℝ V ≤ R.card :=
  finrank_le_quadruples_zeta V ha hV (fun v hv => strip_of_C2 ha (hV v hv) (hc v hv)) hneg R hR

/-- **One strip-test probe with `Q < 0` exhibits an off-line zero of ζ.** -/
theorem exists_offline_of_neg_zeta (ha : 0 < a) {g : ℝ → ℝ} (hp : Probe a g) {K : ℝ}
    (hK : StripTest (fun z => ghatC g a z ^ 2) K) (hneg : weilQ a g < 0) :
    ∃ i, (zetaZeroFamily i).re ≠ 1 / 2 :=
  exists_offline_of_neg hp ha (weilExplicit_of_strip ha hp hK) hneg

/-- **One `C²` probe with `Q < 0` exhibits an off-line zero of ζ.** -/
theorem exists_offline_of_neg_C2 (ha : 0 < a) {g : ℝ → ℝ} (hp : Probe a g)
    (hc : ∃ r g₁ g₂, C2Supp r g g₁ g₂ ∧ 0 ≤ r ∧ r ≤ a) (hneg : weilQ a g < 0) :
    ∃ i, (zetaZeroFamily i).re ≠ 1 / 2 := by
  obtain ⟨K, hK⟩ := strip_of_C2 ha hp hc
  exact exists_offline_of_neg_zeta ha hp hK hneg

end Pilot1ca

#print axioms Pilot1ca.weilExplicit_of_strip
#print axioms Pilot1ca.finrank_le_quadruples_zeta
#print axioms Pilot1ca.finrank_le_offline_zeta
#print axioms Pilot1ca.finrank_le_quadruples_C2
#print axioms Pilot1ca.exists_offline_of_neg_zeta
#print axioms Pilot1ca.exists_offline_of_neg_C2
