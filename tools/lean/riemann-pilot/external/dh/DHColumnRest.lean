import Mathlib
import DHColumn
import DHGround

/-! # The dh column, part 4: the remaining G rows and the strip row of the P block

Nine pilot theorems of the form "hypotheses ⇒ `RiemannHypothesis`" that DHColumn.lean and
DHGround.lean leave without a dh column. Each is restated for the Davenport–Heilbronn function
`dh` (`Xi ↦ XiDH chi5`, `IsGroundState ↦ IsGroundStateDH`, `HypConvStrip ↦ HypConvStripDH`,
`topGS ↦ topGSDH`) and refuted, from DHColumn's and DHGround's refutations or, for the three
Hadamard-parameter rows, from DHColumn's generic lemmas and `XiDH_nonreal_zero`: for `dh`, each
hypothesis set is unsatisfiable. Seven theorems cover the nine rows; two rows get none (below). Every hypothesis of the ζ statement is kept (renamed) unless a landed dh fact
discharges it; the docstrings say which.

Each declaration (left) and the pilot declaration it is the dh column of (right):

* `not_ground_states_dh` — `rh_of_ground_states` (Roadmap.lean:333), via
  `not_realRooted_limit_XiDH` (the column of `rh_of_realRooted_limit`, Roadmap.lean:260)
* `not_groundStates_dodging_dh` — `rh_of_groundStates_dodging` (GroundState.lean:153), via
  `not_dodging_dh` (the column of `rh_of_dodging_final`, Curvature.lean:415)
* `not_D_and_realRooted_hadamard` — `rh_of_D_and_realRooted` (Limit.lean:303), via
  `hypConvDH_of_D` and `not_hypConvDH_of_realRooted`
* `rh_of_D_and_realRooted_final` (XiBounds.lean:360) has no new declaration: its dh column is
  `not_D_and_realRooted` (DHColumn.lean:395), because `hadamard_dh'` discharges the two named `Ξ`
  inputs of `rh_of_D_and_realRooted_proved` (HadamardApply.lean:181) at once, so the `_proved` and
  `_final` rows have one dh column
* `not_hypConvStripDH_top` — `rh_of_hypConvStrip_top` (StripConv.lean:100), via
  `not_hypConvStripDH_of_cross` and `topGSDH_cross` (the strip analogue of `not_hypConvDH_top`)
* `not_XiDH_params` — `rh_of_Xi_params` (Curvature.lean:53), via `real_of_params`
  (DHColumn.lean:425) and `XiDH_nonreal_zero`
* `not_dodging_hadamard` — `rh_of_dodging` (Curvature.lean:86), via `real_of_dodging`
  (DHColumn.lean:452) and `XiDH_nonreal_zero`
* `not_pairing_and_realRooted` — `rh_of_pairing_and_realRooted` (Limit.lean:191), via
  `real_of_pairing` (DHColumn.lean:350) and `XiDH_nonreal_zero`

**No dh column for `rh_grh_of_member_zero` (WeilDedekind.lean:177).** Its hypothesis
`GRHMemberZero` (AngularFamily.lean:97) is GRH for the product `angularL0 = ζ · L(χ₋₄)`
(AngularFamily.lean:39), and its two conclusions `RiemannHypothesis` and `GRH chi4` come from the
two factors: a zero of either factor is a zero of the product. `dh` is a single function, the
linear combination `(1 + ε')L(s, χ₅) + (1 + ε)L(s, χ₅⁻¹)` (`dhL`, DavenportHeilbronn.lean:251), not
a product; a zero of one summand need not be a zero of `dh`, so GRH for `dh` gives nothing about
`L(s, χ₅)` or `L(s, χ₅⁻¹)` and has no second conjunct to give. What remains is the first
conjunct, GRH for `dh` ⇒ `DHRH`, whose refutation is `not_GRH_dh` (DHColumn.lean:566), the dh
column of `rh_of_member_zero` (AngularFamily.lean:102). No declaration is added for this row. -/

open Real Filter Topology Complex MeasureTheory Set

noncomputable section

namespace PsiOmega

open LandauLaplace Pilot1ca Pilot1bt PilotWeil

/-- **The dh column of `rh_of_ground_states`** (Roadmap.lean:333): no integrable `g n` with
real-rooted transforms and nonzero scalars `c n` satisfy `c n · ĝ_n → Ξ_dh` locally uniformly. Every
hypothesis of the ζ statement is kept (`Xi ↦ XiDH chi5`); `RiemannHypothesis ↦ False`. As in the ζ
statement, no ground-state hypothesis is made. -/
theorem not_ground_states_dh {a : ℕ → ℝ} {g : ℕ → ℝ → ℝ}
    (hint : ∀ n, IntervalIntegrable (g n) volume (-(a n)) (a n))
    (hRR : ∀ n, RealRooted (a n) (g n)) {c : ℕ → ℂ} (hc : ∀ n, c n ≠ 0)
    (hconv : TendstoLocallyUniformly (fun n z => c n * ghatC (g n) (a n) z) (XiDH chi5) atTop) :
    False :=
  not_realRooted_limit_XiDH (fun n => ghatC_differentiable (hint n)) (fun n => hRR n) hc hconv

/-- **The dh column of `rh_of_groundStates_dodging`** (GroundState.lean:153): no ground states
`g n` of `QDHu` with `∫g_n ≠ 0` and real-rooted transforms dodge `Ξ_dh`'s zeros in the sense of
`hD`. Every hypothesis of the ζ statement is kept (`IsGroundState ↦ IsGroundStateDH`,
`ZeroIdx (sqF Xi) ↦ ZeroIdx (sqF (XiDH chi5))`); `RiemannHypothesis ↦ False`. As in the ζ proof,
evenness and integrability come from the ground state's probe `(hgs n).1`. -/
theorem not_groundStates_dodging_dh {a : ℕ → ℝ} {g : ℕ → ℝ → ℝ} (ha : ∀ n, 0 ≤ a n)
    (hgs : ∀ n, IsGroundStateDH (a n) (g n))
    (hg0 : ∀ n, (∫ u in (-(a n))..(a n), g n u) ≠ 0)
    (hRR : ∀ n, RealRooted (a n) (g n))
    {t η : ℕ → ℝ}
    (hD : ∀ n, ∃ (p : ZeroIdx (sqF (ghatC (g n) (a n))) → Prop)
      (e : {i // p i} ≃ {j : ZeroIdx (sqF (XiDH chi5)) // t n < ‖j.1⁻¹‖}),
      (∑' i : {i // p i}, ‖i.1.1⁻¹ - (e i).1.1⁻¹‖) ≤ η n)
    (hη : Tendsto η atTop (𝓝 0)) (ht : Tendsto t atTop (𝓝 0)) : False :=
  not_dodging_dh ⟨a, g, t, η, ha, fun n => (probe_integrable (hgs n).1).intervalIntegrable,
    fun n => (hgs n).1.even, hg0, hRR, hD, hη, ht⟩

/-- **The dh column of `rh_of_D_and_realRooted`** (Limit.lean:303): for integrable `g n` with
real-rooted transforms, Hadamard factorisations `hF` of the `ĝ_n` and `hX` of `Ξ_dh`, the uniform
bound `hB` and exact Hypothesis D `hD`, the tails `ε` do not tend to `0`. Every hypothesis of the ζ
statement is kept, including the named input `hX` (`HadamardW Xi v ↦ HadamardW (XiDH chi5) v`, for
an arbitrary zero family `v`; for `Ξ_dh`'s own zero list it is `hadamard_dh'`, which
`not_D_and_realRooted` uses); the last hypothesis `hε` is negated. -/
theorem not_D_and_realRooted_hadamard {a : ℕ → ℝ} {g : ℕ → ℝ → ℝ}
    (hint : ∀ n, IntervalIntegrable (g n) volume (-(a n)) (a n))
    (hRR : ∀ n, RealRooted (a n) (g n))
    {ι : ℕ → Type} {κ : Type} {w : ∀ n, ι n → ℂ} {v : κ → ℂ}
    (hF : ∀ n, HadamardW (ghatC (g n) (a n)) (w n)) (hX : HadamardW (XiDH chi5) v)
    {B : ℝ} (hB : ∀ n, (∑' i, ‖w n i‖) ≤ B) {t : ℕ → ℝ} (hD : ∀ n, DFamW (w n) v (t n)) :
    ¬ Tendsto (fun n => tailEps (w n) v (t n)) atTop (𝓝 0) := fun hε =>
  not_hypConvDH_of_realRooted hint (Eventually.of_forall hRR) (hypConvDH_of_D hF hX hB hD hε)

/-- **The dh column of `rh_of_hypConvStrip_top`** (StripConv.lean:100): `HypConvStripDH` at
DHColumn's width `2` fails for the top-of-chain ground states of `QDHu`, at every sequence of
positive supports (the strip analogue of `not_hypConvDH_top`). The hypothesis `ha` is kept;
`HypConvStrip ↦ HypConvStripDH · · 2`, `topGS ↦ topGSDH`. The ζ proof's real-zero input
`zetaNoZeroInUnitInterval` has no counterpart: `not_hypConvStripDH_of_cross` refutes the cross
conclusion with the non-real off-line zero `dh_offline_nonreal_zero`. -/
theorem not_hypConvStripDH_top {a : ℕ → ℝ} (ha : ∀ n, 0 < a n) :
    ¬ HypConvStripDH a (fun n => topGSDH (a n)) 2 :=
  not_hypConvStripDH_of_cross
    (fun n => (probe_integrable (topGSDH_isGroundState (ha n)).1).intervalIntegrable)
    (Eventually.of_forall fun n z hz => topGSDH_cross (ha n) z hz)

/-- **The dh column of `rh_of_Xi_params`** (Curvature.lean:53): no Hadamard factorisation of
`Ξ_dh` has every parameter a non-negative real. Every hypothesis of the ζ statement is kept
(`HadamardW Xi v ↦ HadamardW (XiDH chi5) v`); `RiemannHypothesis ↦ False`. -/
theorem not_XiDH_params {κ : Type*} {v : κ → ℂ} (hX : HadamardW (XiDH chi5) v)
    (hv : ∀ j, (v j).im = 0 ∧ 0 ≤ (v j).re) : False := by
  obtain ⟨z, hz, him⟩ := XiDH_nonreal_zero
  exact him (real_of_params hX hv z hz)

/-- **The dh column of `rh_of_dodging`** (Curvature.lean:86): no real-rooted family with Hadamard
factorisations `hF` of the `ĝ_n` dodges the parameters of a Hadamard factorisation `hX` of `Ξ_dh` in
the sense of `hD`. Every hypothesis of the ζ statement is kept, including the named inputs `hF` and
`hX` (`HadamardW Xi v ↦ HadamardW (XiDH chi5) v`, for an arbitrary parameter family `v`);
`RiemannHypothesis ↦ False`. For the factorisations over the zero lists (`hadamardW_ghat`,
`hadamard_dh'`) this is `not_dodging_dh`. -/
theorem not_dodging_hadamard {a : ℕ → ℝ} {g : ℕ → ℝ → ℝ} (hRR : ∀ n, RealRooted (a n) (g n))
    {ι : ℕ → Type} {κ : Type} {w : ∀ n, ι n → ℂ} {v : κ → ℂ}
    (hF : ∀ n, HadamardW (ghatC (g n) (a n)) (w n)) (hX : HadamardW (XiDH chi5) v)
    {t η : ℕ → ℝ}
    (hD : ∀ n, ∃ (p : ι n → Prop) (e : {i // p i} ≃ {j // t n < ‖v j‖}),
      (∑' i : {i // p i}, ‖w n i - v (e i)‖) ≤ η n)
    (hη : Tendsto η atTop (𝓝 0)) (ht : Tendsto t atTop (𝓝 0)) : False := by
  obtain ⟨z, hz, him⟩ := XiDH_nonreal_zero
  exact him (real_of_dodging hRR hF hX hD hη ht z hz)

/-- **The dh column of `rh_of_pairing_and_realRooted`** (Limit.lean:191): for integrable `g n` with
real-rooted transforms, Hadamard factorisations `hF` of the `ĝ_n` and `hX n` of `Ξ_dh`, and the
uniform bound `hB`, the pairing errors `θ` do not tend to `0`. Every hypothesis of the ζ statement
is kept, including the named inputs `hF` and `hX` (`HadamardW Xi (v n) ↦ HadamardW (XiDH chi5)
(v n)`); the last hypothesis `hθ0` is negated. The entireness of the limit, which the ζ proof takes
from `differentiable_Xi`, is `differentiable_XiDH_chi5`. -/
theorem not_pairing_and_realRooted {a : ℕ → ℝ} {g : ℕ → ℝ → ℝ}
    (hint : ∀ n, IntervalIntegrable (g n) volume (-(a n)) (a n))
    (hRR : ∀ n, RealRooted (a n) (g n))
    {ι : ℕ → Type*} {w v : ∀ n, ι n → ℂ}
    (hF : ∀ n, HadamardW (ghatC (g n) (a n)) (w n)) (hX : ∀ n, HadamardW (XiDH chi5) (v n))
    {B : ℝ} (hB : ∀ n, (∑' i, ‖w n i‖) ≤ B) {θ : ℕ → ℝ}
    (hθ : ∀ n, (∑' i, ‖w n i - v n i‖) ≤ θ n) : ¬ Tendsto θ atTop (𝓝 0) := fun hθ0 => by
  obtain ⟨z, hz, him⟩ := XiDH_nonreal_zero
  exact him (real_of_pairing differentiable_XiDH_chi5 hint hRR hF hX hB hθ hθ0 z hz)

end PsiOmega

#print axioms PsiOmega.not_ground_states_dh
#print axioms PsiOmega.not_groundStates_dodging_dh
#print axioms PsiOmega.not_D_and_realRooted_hadamard
#print axioms PsiOmega.not_hypConvStripDH_top
#print axioms PsiOmega.not_XiDH_params
#print axioms PsiOmega.not_dodging_hadamard
#print axioms PsiOmega.not_pairing_and_realRooted
