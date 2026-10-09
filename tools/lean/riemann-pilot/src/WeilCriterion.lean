import Mathlib
import WeilZeta
import Unconditional

/-! # Weil's criterion for `ζ`, with no named input (round 157)

Round 131 (`WeilConverse.lean`) proved, for any zero family satisfying the explicit formula, that
finitely many off-line zeros make Weil's form negative somewhere. The proof uses the formula only
for the box `box 1` and its twins. Both are strip test functions: an even, nonnegative profile that
is non-increasing on `[0, a]` has `‖ĝ(z)‖ ≤ 2g(0)cosh(a Im z)/‖z‖` (`norm_ghatC_le_of_antitone`,
round 37), so `ĝ²` decays like `1/(Re z)²` on the strip. Round 156's `weilExplicit_zeta` then
supplies both instances over the zeros of `ζ`.

* `ghat_antitone_strip`, `striptest_antitone`: `ĝ²` is in the strip class for every such profile.
* `weilExplicit_antitone_zeta`: the explicit formula over the zeros of `ζ` for every such probe.
* `weilExplicit_box_zeta`, `weilExplicit_twinbox_zeta`: the two instances Weil's criterion needs.
* `im_zetaZeroFamily_ne`: no nontrivial zero is real.

Round 157 also proved Weil's criterion here in finite-exception form (`rh_of_weil_finite`, which
needed `hfin`: finitely many off-line zeros). Round 220's `WeilLandau.rh_of_weil` supersedes it with
no finiteness hypothesis.
-/

open Real Filter Topology Complex Set MeasureTheory

noncomputable section

namespace Pilot1ca

open Pilot1bt PilotWeil

/-! ## Monotone profiles are strip test functions -/

/-- **`ĝ` on the strip from a `1/‖z‖` bound**: if `‖ĝ(z)‖ ≤ B/‖z‖` for `z ≠ 0` on the strip, then
`‖ĝ(z)‖²(1 + (Re z)²) ≤ K` there. -/
theorem ghat_strip_of_inv {g : ℝ → ℝ} {a B : ℝ} (ha : 0 ≤ a) (hB : 0 ≤ B)
    (hint : IntervalIntegrable g volume (-a) a)
    (hb : ∀ t ∈ PilotWeil.strip (-1) 1, t ≠ 0 → ‖ghatC g a t‖ ≤ B / ‖t‖) :
    ∃ K, ∀ t ∈ PilotWeil.strip (-1) 1, ‖ghatC g a t‖ ^ 2 * (1 + t.re ^ 2) ≤ K := by
  refine ⟨(Real.exp a * ∫ u in (-a)..a, |g u|) ^ 2 + B ^ 2, fun t ht => sq_strip_bound
    (norm_ghatC_strip_le ha hint (abs_le.2 ⟨ht.1, ht.2⟩)) ?_⟩
  rcases eq_or_ne t 0 with rfl | ht0
  · simpa using hB
  have hn : 0 < ‖t‖ := norm_pos_iff.2 ht0
  have := hb t ht ht0
  rw [le_div_iff₀ hn] at this
  linarith [mul_comm ‖t‖ ‖ghatC g a t‖]

/-- **`ĝ` on the strip for a monotone profile**: `‖ĝ(z)‖²(1 + (Re z)²) ≤ K` on `|Im z| ≤ 1`. -/
theorem ghat_antitone_strip {g : ℝ → ℝ} {a : ℝ} (ha : 0 < a) (hev : ∀ u, g (-u) = g u)
    (hmono : AntitoneOn g (Icc 0 a)) (hnn : ∀ u ∈ Icc 0 a, 0 ≤ g u)
    (hint : IntervalIntegrable g volume (-a) a) : ∃ K, ∀ t ∈ PilotWeil.strip (-1) 1,
    ‖ghatC g a t‖ ^ 2 * (1 + t.re ^ 2) ≤ K := by
  have hg0 : 0 ≤ g 0 := hnn 0 ⟨le_rfl, ha.le⟩
  refine ghat_strip_of_inv ha.le (B := 2 * g 0 * Real.cosh a) (by positivity) hint fun t ht ht0 => ?_
  refine (norm_ghatC_le_of_antitone ha hev hmono hnn ht0).trans
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (by positivity)) (norm_nonneg _))
  rw [Real.cosh_le_cosh, abs_mul, abs_of_pos ha, abs_abs]
  exact mul_le_of_le_one_right ha.le (abs_le.2 ⟨ht.1, ht.2⟩)

/-- **`ĝ²` is a strip test function** for every even, nonnegative profile non-increasing on `[0, a]`. -/
theorem striptest_antitone {g : ℝ → ℝ} {a : ℝ} (ha : 0 < a) (hev : ∀ u, g (-u) = g u)
    (hmono : AntitoneOn g (Icc 0 a)) (hnn : ∀ u ∈ Icc 0 a, 0 ≤ g u)
    (hint : IntervalIntegrable g volume (-a) a) : ∃ K, StripTest (fun z => ghatC g a z ^ 2) K := by
  obtain ⟨K, hK⟩ := ghat_antitone_strip ha hev hmono hnn hint
  exact ⟨K, striptest_sq (ghatC_differentiable hint) hK⟩

/-- **The explicit formula over the zeros of `ζ`** for every monotone probe: no named input. -/
theorem weilExplicit_antitone_zeta {g : ℝ → ℝ} {a : ℝ} (ha : 0 < a) (hp : Probe a g)
    (hmono : AntitoneOn g (Icc 0 a)) (hnn : ∀ u ∈ Icc 0 a, 0 ≤ g u) :
    WeilExplicit zetaZeroFamily (fun z => ghatC g a z ^ 2) (hsq g a) := by
  obtain ⟨K, hK⟩ := striptest_antitone ha hp.even hmono hnn hp.intervalIntegrable
  exact weilExplicit_zeta hK (fun t => even_ghat_sq hp.even a t) (hsq_ofReal hp ha.le)

/-! ## The box and its twins -/

theorem box_antitone : AntitoneOn (box 1) (Icc 0 1) := fun x hx y hy _ => by
  have h1 : |x| ≤ 1 := by rw [abs_of_nonneg hx.1]; exact hx.2
  have h2 : |y| ≤ 1 := by rw [abs_of_nonneg hy.1]; exact hy.2
  rw [box_apply, box_apply]; simp [h1, h2]

theorem box_nonneg : ∀ u ∈ Icc (0 : ℝ) 1, 0 ≤ box 1 u := fun u _ => by
  rw [box_apply]; split_ifs <;> positivity

/-- The explicit formula for `ĝ_box²` over the zeros of `ζ`. -/
theorem weilExplicit_box_zeta :
    WeilExplicit zetaZeroFamily (fun z => ghatC (box 1) 1 z ^ 2) (hsq (box 1) 1) :=
  weilExplicit_antitone_zeta one_pos (box_probe 1) box_antitone box_nonneg

/-- The explicit formula for the twin boxes' `ĝ²` over the zeros of `ζ`. -/
theorem weilExplicit_twinbox_zeta {l : ℝ} (hl : 0 ≤ l) :
    WeilExplicit zetaZeroFamily (fun z => ghatC (twin (box 1) l) (l + 1) z ^ 2)
      (hsq (twin (box 1) l) (l + 1)) :=

  weilExplicit_twin_gen weilExplicit_zeta one_pos (box_probe 1) hl
    (ghat_antitone_strip one_pos (box_probe 1).even box_antitone box_nonneg
      (box_probe 1).intervalIntegrable).choose_spec

/-! ## No nontrivial zero is real -/

/-- No nontrivial zero of `ζ` is real (`ζ ≠ 0` on `(0, 1)`). -/
theorem im_zetaZeroFamily_ne (i : Σ w : NontrivialZero, Fin (zeroMult w)) :
    (zetaZeroFamily i).im ≠ 0 := by
  intro h
  have hz := i.1.2
  have e : zetaZeroFamily i = ((zetaZeroFamily i).re : ℂ) := Complex.ext (by simp) (by simp [h])
  have h0 := hz.1
  change riemannZeta (zetaZeroFamily i) = 0 at h0
  rw [e] at h0
  exact zetaNoZeroInUnitInterval _ hz.re_pos hz.re_lt_one h0

end Pilot1ca

#print axioms Pilot1ca.striptest_antitone
#print axioms Pilot1ca.weilExplicit_antitone_zeta
#print axioms Pilot1ca.weilExplicit_twinbox_zeta
