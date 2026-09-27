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
* `exists_weilQ_neg_of_offline_zeta`: if all but finitely many nontrivial zeros of `ζ` lie on the
  critical line and one does not, some probe has `Q < 0`.
* `rh_of_weil_finite`: `Q ≥ 0` for every probe, and finitely many off-line zeros, give Mathlib's
  `RiemannHypothesis`.

This is Weil's criterion in finite-exception form, unconditionally. It is an equivalence-type
statement: it has no bearing on RH.
-/

open Real Filter Topology Complex Set MeasureTheory

noncomputable section

namespace Pilot1ca

open Pilot1bt PilotWeil

/-! ## Monotone profiles are strip test functions -/

/-- **The strip bound from two pointwise bounds**: `‖G‖ ≤ τ₀` and `‖t‖‖G‖ ≤ τ₁` on the strip give
`‖G‖²(1 + (Re t)²) ≤ τ₀² + τ₁²`. -/
theorem sq_strip_bound {G : ℂ → ℂ} {τ0 τ1 : ℝ} {t : ℂ} (h0 : ‖G t‖ ≤ τ0)
    (h1 : ‖t‖ * ‖G t‖ ≤ τ1) : ‖G t‖ ^ 2 * (1 + t.re ^ 2) ≤ τ0 ^ 2 + τ1 ^ 2 := by
  have hx : t.re ^ 2 ≤ ‖t‖ ^ 2 := by
    have := Complex.abs_re_le_norm t
    nlinarith [abs_nonneg t.re, sq_abs t.re]
  have hgn := norm_nonneg (G t)
  have hτ0 : 0 ≤ τ0 := le_trans hgn h0
  nlinarith [mul_le_mul h0 h0 hgn hτ0, mul_self_nonneg (‖t‖ * ‖G t‖),
    mul_le_mul h1 h1 (by positivity) (le_trans (by positivity) h1)]

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
      (hsq (twin (box 1) l) (l + 1)) := by
  have hp := box_probe 1
  have hpt := twin_probe hp hl
  obtain ⟨K, hK⟩ := ghat_antitone_strip one_pos hp.even box_antitone box_nonneg hp.intervalIntegrable
  have hT := striptest_mul_sq (G := ghatC (box 1) 1) (m := fun z => 2 * Complex.cos (l * z))
    (ghatC_differentiable hp.intervalIntegrable) (by fun_prop) hK (fun t ht => norm_two_cos_strip hl ht)
  have e : (fun z => ghatC (twin (box 1) l) (l + 1) z ^ 2)
      = fun z => (2 * Complex.cos (l * z) * ghatC (box 1) 1 z) ^ 2 := by
    funext z; rw [ghatC_twin one_pos hp hl]
  rw [e]
  refine weilExplicit_zeta hT (fun t => ?_) (fun r => ?_)
  · have := even_ghat_sq hpt.even (l + 1) t
    rw [ghatC_twin one_pos hp hl, ghatC_twin one_pos hp hl] at this
    exact this
  · have := hsq_ofReal hpt (by linarith) r
    rw [ghatC_twin one_pos hp hl] at this
    exact this

/-! ## Weil's criterion, finite-exception form, for `ζ` -/

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

/-- **An off-line zero of `ζ` makes Weil's form negative, unconditionally.** If all but finitely
many nontrivial zeros lie on the critical line and one does not, some probe has `Q < 0`. -/
theorem exists_weilQ_neg_of_offline_zeta (F : Finset (Σ w : NontrivialZero, Fin (zeroMult w)))
    (hF : ∀ i ∉ F, (zetaZeroFamily i).re = 1 / 2) (hoff : ∃ i ∈ F, (zetaZeroFamily i).re ≠ 1 / 2) :
    ∃ a g, 0 < a ∧ Probe a g ∧ weilQ a g < 0 :=
  exists_weilQ_neg_of_offline_of weilExplicit_box_zeta (fun _ hl => weilExplicit_twinbox_zeta hl)
    F hF (fun i _ => im_zetaZeroFamily_ne i) hoff

/-- **Weil's criterion for `ζ`, finite-exception form, no named input.** If `Q ≥ 0` for every probe
at every support and only finitely many nontrivial zeros of `ζ` lie off the critical line, then
Mathlib's `RiemannHypothesis` holds. -/
theorem rh_of_weil_finite (hQ : ∀ (a : ℝ) (g : ℝ → ℝ), 0 < a → Probe a g → 0 ≤ weilQ a g)
    (hfin : {s : ℂ | IsNontrivialZero s ∧ s.re ≠ 1 / 2}.Finite) : RiemannHypothesis := by
  classical
  set S := {s : ℂ | IsNontrivialZero s ∧ s.re ≠ 1 / 2}
  have hZ : {w : NontrivialZero | w.1 ∈ S}.Finite := hfin.preimage Subtype.val_injective.injOn
  have hI : (zetaZeroFamily ⁻¹' S).Finite := by
    refine (hZ.biUnion fun w _ => Set.finite_range (fun k : Fin (zeroMult w) => (⟨w, k⟩ :
      Σ w : NontrivialZero, Fin (zeroMult w)))).subset fun i hi => ?_
    exact Set.mem_biUnion (x := i.1) hi ⟨i.2, rfl⟩
  have hline : ∀ i, (zetaZeroFamily i).re = 1 / 2 := by
    by_contra h
    push Not at h
    obtain ⟨i, hi⟩ := h
    have hF : ∀ j ∉ hI.toFinset, (zetaZeroFamily j).re = 1 / 2 := fun j hj => by
      by_contra h'
      exact hj (hI.mem_toFinset.2 ⟨j.1.2, h'⟩)
    obtain ⟨a, g, ha, hp, hneg⟩ := exists_weilQ_neg_of_offline_zeta hI.toFinset hF
      ⟨i, hI.mem_toFinset.2 ⟨i.1.2, hi⟩, hi⟩
    exact absurd (hQ a g ha hp) (not_le.2 hneg)
  intro s hs htriv _
  exact hline ⟨⟨s, hs, htriv⟩, ⟨0, zeroMult_pos _⟩⟩

end Pilot1ca

#print axioms Pilot1ca.striptest_antitone
#print axioms Pilot1ca.weilExplicit_antitone_zeta
#print axioms Pilot1ca.weilExplicit_twinbox_zeta
#print axioms Pilot1ca.exists_weilQ_neg_of_offline_zeta
#print axioms Pilot1ca.rh_of_weil_finite
