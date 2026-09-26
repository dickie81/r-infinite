import Mathlib
import PrimeSide
import ZeroSwap

/-! # The chain with zeros on `ℝ ∪ iℝ`

Hurwitz's theorem for a closed target set (`hurwitz_closed`, Roadmap.lean) carries "every zero of
`ĝ_n` lies in `S`" to the limit.

`rh_of_prime_side_cross`: the chain of `rh_of_prime_side` with (b) weakened to "every zero of `ĝ_n`
is real or purely imaginary", which is what the zero-swap lemma (ZeroSwap.lean) gives. A zero of `Ξ`
on the imaginary axis is a real zero of `ζ` in `(0, 1)`. Excluding those is the named input
`ZetaNoZeroInUnitInterval`, now proved (`zetaNoZeroInUnitInterval`, from `Φ > 0` in RiemannKernel.lean).

`rh_of_simple_ground_states`: the chain stated with the zero-swap lemma plugged in.
`rh_of_simple_ground_states'`: the same with `ζ ≠ 0` on `(0, 1)` discharged. Its only inputs are
(a), eventual simplicity and the swap realisation. SwapRealize.lean proves the swap realisation and
states the chain without it (`rh_of_eventually_simple`).
-/

open Real Filter Topology Complex MeasureTheory Set

noncomputable section

namespace Pilot1ca

open Pilot1bt

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
  have h0 := hconv.eventually_ne
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

/-- **§11 item 1 ⇒ RH, with prime-side hypotheses only.** Ground states of Weil's form `Q` at
supports `2a n` whose transforms are eventually real-rooted (b) and satisfy `HypConv` (a) give
Mathlib's `RiemannHypothesis`. The case of `rh_of_prime_side_cross` with every zero real. -/
theorem rh_of_prime_side {a : ℕ → ℝ} {g : ℕ → ℝ → ℝ} (hgs : ∀ n, IsGroundState (a n) (g n))
    (hRR : ∀ᶠ n in atTop, RealRooted (a n) (g n)) (hconv : HypConv a g) : RiemannHypothesis :=
  rh_of_prime_side_cross hgs (hRR.mono fun _ h z hz => Or.inr (h z hz)) hconv
    (fun _ h0 h1 => riemannZeta_ne_zero_of_mem_Ioo h0 h1)

/-- **The chain with the zero-swap lemma plugged in.** (a), positive supports, eventually simple
ground states with the swap realised (proved in SwapRealize.lean) and no zero of `ζ` in `(0, 1)`
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

/-- **`ζ(σ) ≠ 0` on `(0, 1)`, proved** (`riemannZeta_ne_zero_of_mem_Ioo`, RiemannKernel.lean). -/
theorem zetaNoZeroInUnitInterval : ZetaNoZeroInUnitInterval :=
  fun _ h0 h1 => riemannZeta_ne_zero_of_mem_Ioo h0 h1

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

#print axioms Pilot1ca.isClosed_crossSet
#print axioms Pilot1ca.rh_of_prime_side_cross
#print axioms Pilot1ca.rh_of_prime_side
#print axioms Pilot1ca.rh_of_simple_ground_states
#print axioms Pilot1ca.zetaNoZeroInUnitInterval
#print axioms Pilot1ca.rh_of_simple_ground_states'
