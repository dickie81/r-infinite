import Mathlib
import PrimeSide
import ZeroSwap
import ZetaUnitInterval

/-! # Hurwitz for closed sets, and the chain with zeros on `ℝ ∪ iℝ`

`hurwitz_closed`: if entire `F n → f` locally uniformly, `f ≢ 0`, and every zero of every `F n`
lies in a closed set `S`, then every zero of `f` lies in `S`. `hurwitz_real` (Roadmap.lean) is the
case `S = ℝ`; the proof is the same maximum-modulus argument, with the disc chosen inside `Sᶜ`.

`rh_of_prime_side_cross`: the chain of `rh_of_prime_side` with (b) weakened to "every zero of `ĝ_n`
is real or purely imaginary", which is what the zero-swap lemma (ZeroSwap.lean) gives. A zero of `Ξ`
on the imaginary axis is a real zero of `ζ` in `(0, 1)`. Excluding those is the named input
`ZetaNoZeroInUnitInterval`, now proved (`zetaNoZeroInUnitInterval`, from ZetaUnitInterval.lean).

`rh_of_simple_ground_states`: the chain stated with the zero-swap lemma plugged in.
`rh_of_simple_ground_states'`: the same with `ζ ≠ 0` on `(0, 1)` discharged. Its only inputs are
(a), eventual simplicity and the swap realisation (Paley–Wiener, named in ZeroSwap.lean).
-/

open Real Filter Topology Complex MeasureTheory Set

noncomputable section

namespace Pilot1ca

open Pilot1bt

/-- **Hurwitz for a closed set.** -/
theorem hurwitz_closed {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ} (hF : ∀ n, Differentiable ℂ (F n))
    (hf : Differentiable ℂ f) (hconv : TendstoLocallyUniformly F f atTop)
    (hnz : ∃ w, f w ≠ 0) {S : Set ℂ} (hS : IsClosed S) (hzeros : ∀ n z, F n z = 0 → z ∈ S) :
    ∀ z₀, f z₀ = 0 → z₀ ∈ S := by
  intro z₀ hz₀
  by_contra hS0
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 hS.isOpen_compl z₀ hS0
  -- `z₀` is an isolated zero
  have hiso : ∀ᶠ z in 𝓝[≠] z₀, f z ≠ 0 := by
    rcases (hf.analyticAt z₀).eventually_eq_zero_or_eventually_ne_zero with h | h
    · exfalso
      obtain ⟨w, hw⟩ := hnz
      have hall := (hf.differentiableOn.analyticOnNhd isOpen_univ).eqOn_zero_of_preconnected_of_eventuallyEq_zero
        isPreconnected_univ (Set.mem_univ z₀) (h.mono fun z hz => by simp [hz])
      exact hw (by simpa using hall (Set.mem_univ w))
    · exact h
  obtain ⟨ε, hε, hεf⟩ := Metric.eventually_nhds_iff.1 (eventually_nhdsWithin_iff.1 hiso)
  set r := min (ε / 2) (ρ / 2) with hr_def
  have hr : 0 < r := lt_min (by linarith) (by linarith)
  have hrε : r < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hrρ : r < ρ := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  -- `|f| ≥ m > 0` on the circle
  have hne : (Metric.sphere z₀ r).Nonempty := ⟨z₀ + r, by simp [abs_of_pos hr]⟩
  obtain ⟨w, hwS, hwmin⟩ := (isCompact_sphere z₀ r).exists_isMinOn hne
    (hf.continuous.norm.continuousOn)
  have hfS : ∀ z ∈ Metric.sphere z₀ r, f z ≠ 0 := by
    intro z hz
    rw [mem_sphere_iff_norm] at hz
    apply hεf (by rw [dist_eq_norm, hz]; exact hrε)
    intro h; rw [h, sub_self, norm_zero] at hz; exact hr.ne hz
  set m := ‖f w‖ with hm_def
  have hm : 0 < m := norm_pos_iff.2 (hfS w hwS)
  have hunif := (tendstoLocallyUniformly_iff_forall_isCompact.1 hconv) _
    (isCompact_closedBall z₀ r)
  obtain ⟨n, hn⟩ := (Metric.tendstoUniformlyOn_iff.1 hunif (m / 2) (by linarith)).exists
  -- `F n` has no zero on the closed disc: the disc lies in `Sᶜ`
  have hnoz : ∀ z ∈ Metric.closedBall z₀ r, F n z ≠ 0 := by
    intro z hz h
    have hzS := hzeros n z h
    have : z ∈ Metric.ball z₀ ρ := lt_of_le_of_lt (Metric.mem_closedBall.1 hz) hrρ
    exact hball this hzS
  have hbound : ∀ z ∈ frontier (Metric.ball z₀ r), ‖(F n z)⁻¹‖ ≤ (m / 2)⁻¹ := by
    intro z hz
    rw [frontier_ball z₀ hr.ne'] at hz
    have h1 := hn z (Metric.sphere_subset_closedBall hz)
    have h2 : m ≤ ‖f z‖ := hwmin hz
    rw [dist_eq_norm] at h1
    have h3 : m / 2 ≤ ‖F n z‖ := by
      have := norm_sub_norm_le (f z) (F n z)
      linarith
    rw [norm_inv]
    exact inv_anti₀ (by linarith) h3
  have hdiff : DiffContOnCl ℂ (fun z => (F n z)⁻¹) (Metric.ball z₀ r) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball z₀ hr.ne']
    exact ((hF n).differentiableOn).inv hnoz
  have hmax := Complex.norm_le_of_forall_mem_frontier_norm_le Metric.isBounded_ball hdiff hbound
    (subset_closure (Metric.mem_ball_self hr))
  have hz0 := hn z₀ (Metric.mem_closedBall_self hr.le)
  rw [hz₀, dist_eq_norm, zero_sub, norm_neg] at hz0
  have hFz0 : F n z₀ ≠ 0 := hnoz z₀ (Metric.mem_closedBall_self hr.le)
  rw [norm_inv] at hmax
  have hpos : 0 < ‖F n z₀‖ := norm_pos_iff.2 hFz0
  have := (inv_le_inv₀ hpos (by linarith)).1 hmax
  linarith

/-- The cross `ℝ ∪ iℝ`. -/
def crossSet : Set ℂ := {z | z.re = 0 ∨ z.im = 0}

theorem isClosed_crossSet : IsClosed crossSet :=
  (isClosed_eq continuous_re continuous_const).union (isClosed_eq continuous_im continuous_const)

/-- `ζ` has no zero in `(0, 1)` (proved below as `zetaNoZeroInUnitInterval`). -/
def ZetaNoZeroInUnitInterval : Prop :=
  ∀ σ : ℝ, 0 < σ → σ < 1 → riemannZeta (σ : ℂ) ≠ 0

theorem re_ordinate (s : ℂ) : ((s - 1 / 2) / I).re = s.im := by
  have e : (s - 1 / 2) / I = -I * (s - 1 / 2) := by field_simp; rw [I_sq]; ring
  rw [e]; simp

/-- **The chain with zeros on the cross.** (a), eventually every zero of `ĝ_n` on `ℝ ∪ iℝ`, and no
zero of `ζ` in `(0, 1)` give Mathlib's `RiemannHypothesis`. -/
theorem rh_of_prime_side_cross {a : ℕ → ℝ} {g : ℕ → ℝ → ℝ}
    (hgs : ∀ n, IsGroundState (a n) (g n))
    (hcross : ∀ᶠ n in atTop, ∀ z, ghatC (g n) (a n) z = 0 → z.re = 0 ∨ z.im = 0)
    (hconv : HypConv a g) (hζ : ZetaNoZeroInUnitInterval) : RiemannHypothesis := by
  have hX0 := Xi_zero_ne_zero
  have h0 : ∀ᶠ n in atTop, ghatC (g n) (a n) 0 ≠ 0 := by
    have hc : TendstoLocallyUniformly (fun n z => ghatC (g n) (a n) z / ghatC (g n) (a n) 0)
      (fun z => Xi z / Xi 0) atTop := hconv
    have hu := Metric.tendstoUniformlyOn_iff.1
      ((tendstoLocallyUniformly_iff_forall_isCompact.1 hc) {0} isCompact_singleton) 1 one_pos
    filter_upwards [hu] with n hn h
    have := hn 0 rfl
    simp only [div_self hX0, h, div_zero, dist_zero_right, norm_one] at this
    exact lt_irrefl _ this
  obtain ⟨N, hN⟩ := (hcross.and h0).exists_forall_of_atTop
  have hint : ∀ n, IntervalIntegrable (g n) volume (-(a n)) (a n) :=
    fun n => (probe_integrable (hgs n).1).intervalIntegrable
  have hXc : ∀ z, Xi z / Xi 0 = 0 → z ∈ crossSet :=
    hurwitz_closed (F := fun m z => ghatC (g (m + N)) (a (m + N)) z / ghatC (g (m + N)) (a (m + N)) 0)
      (fun m => (ghatC_differentiable (hint _)).div_const _)
      (differentiable_Xi.div_const _) (tendstoLocallyUniformly_shift hconv N)
      ⟨0, by rw [div_self hX0]; exact one_ne_zero⟩ isClosed_crossSet
      (fun m z h => (hN (m + N) (by omega)).1 z
        ((div_eq_zero_iff.1 h).resolve_right (hN (m + N) (by omega)).2))
  intro s hz htriv _
  have hs : IsNontrivialZero s := ⟨hz, htriv⟩
  have hc := hXc ((s - 1 / 2) / I)
    (by rw [Xi_at_ordinate, xi_eq_zero_of_nontrivial hs, zero_div])
  rcases hc with hre | him
  · -- a zero on the imaginary axis is a real zero of `ζ` in `(0, 1)`
    exfalso
    rw [re_ordinate] at hre
    obtain ⟨h0', h1'⟩ := hs.mem_strip
    have hsr : s = ((s.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [hre])
    apply hζ s.re h0' h1'
    rw [← hsr]; exact hz
  · exact re_eq_half_of_Xi_real him

/-- **The chain with the zero-swap lemma plugged in.** (a), positive supports, eventually simple
ground states with the swap realised (ZeroSwap.lean's named input) and no zero of `ζ` in `(0, 1)`
give Mathlib's `RiemannHypothesis`. -/
theorem rh_of_simple_ground_states {a : ℕ → ℝ} {g : ℕ → ℝ → ℝ} (ha : ∀ n, 0 < a n)
    (hgs : ∀ n, IsGroundState (a n) (g n))
    (hsimple : ∀ᶠ n in atTop, SimpleGround (a n) (g n))
    (hPW : ∀ᶠ n in atTop, ∀ w : ℂ, ghatC (g n) (a n) w = 0 → (w ^ 2).im ≠ 0 →
      SwapRealization (a n) (g n) (w ^ 2))
    (hconv : HypConv a g) (hζ : ZetaNoZeroInUnitInterval) : RiemannHypothesis := by
  refine rh_of_prime_side_cross hgs ?_ hconv hζ
  filter_upwards [hsimple, hPW] with n hs hp
  exact zeros_real_or_imag (ha n) hs hp

/-- **`ζ(σ) ≠ 0` on `(0, 1)`, proved** (ZetaUnitInterval.lean). -/
theorem zetaNoZeroInUnitInterval : ZetaNoZeroInUnitInterval :=
  fun _ h0 h1 => ZetaUnitInterval.riemannZeta_ne_zero_of_mem_Ioo h0 h1

/-- **The chain, with `ζ ≠ 0` on `(0, 1)` discharged.** (a), positive supports, and eventually simple
ground states with the swap realised give Mathlib's `RiemannHypothesis`. -/
theorem rh_of_simple_ground_states' {a : ℕ → ℝ} {g : ℕ → ℝ → ℝ} (ha : ∀ n, 0 < a n)
    (hgs : ∀ n, IsGroundState (a n) (g n))
    (hsimple : ∀ᶠ n in atTop, SimpleGround (a n) (g n))
    (hPW : ∀ᶠ n in atTop, ∀ w : ℂ, ghatC (g n) (a n) w = 0 → (w ^ 2).im ≠ 0 →
      SwapRealization (a n) (g n) (w ^ 2))
    (hconv : HypConv a g) : RiemannHypothesis :=
  rh_of_simple_ground_states ha hgs hsimple hPW hconv zetaNoZeroInUnitInterval

end Pilot1ca

#print axioms Pilot1ca.hurwitz_closed
#print axioms Pilot1ca.isClosed_crossSet
#print axioms Pilot1ca.rh_of_prime_side_cross
#print axioms Pilot1ca.rh_of_simple_ground_states
#print axioms Pilot1ca.zetaNoZeroInUnitInterval
#print axioms Pilot1ca.rh_of_simple_ground_states'
