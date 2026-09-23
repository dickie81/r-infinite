import Mathlib
import Positivity
import Concave

/-! # §11 item 1, restated with prime-side hypotheses only

The chain to `RiemannHypothesis` used to carry Hypothesis D (`DFamW`, `HypD`). D says the zeros of
`ĝ_n` below `T_D` *are* the zeros of `ζ`, so it presupposes the zeros it is meant to locate. Here
the chain is restated so that no zero of `ζ` appears in any hypothesis:

* **(a) `HypConv`**: the normalised ground-state transforms converge, `ĝ_n(z)/ĝ_n(0) → Ξ(z)/Ξ(0)`,
  locally uniformly. `Ξ` is Riemann's function, built from `completedRiemannZeta₀`, so this is a
  statement about one explicit entire function. No zero, and no zero count, enters.
* **(b) `RealRooted`**, eventually in `n`.

`rh_of_prime_side`: (a) + (b) for ground states of Weil's form at supports `2a n` gives Mathlib's
`RiemannHypothesis`. Nothing else is assumed: `ĝ_n(0) ≠ 0` eventually follows from (a) at `z = 0`,
and `Ξ(0) ≠ 0` is `Xi_zero_ne_zero`.

`hypConv_of_D`: the old route is a special case. D with vanishing tails implies (a) (1bu(ii)). So
the open problem is exactly (a) and (b), and D is one sufficient condition for (a), a
zero-dependent one.

`realRooted_of_polya_shape`: (b) holds at any support where the ground state lies in Pólya's
class (`Polya.lean`). `realRooted_of_ae_concaveOn` (`Concave.lean`) states the same thing directly
for concavity. -/

open Real Filter Topology MeasureTheory Complex

noncomputable section

namespace Pilot1ca

open Pilot1bt

/-- **Item 1(a), zero-free**: the normalised ground-state transforms converge to `Ξ/Ξ(0)` locally
uniformly. -/
def HypConv (a : ℕ → ℝ) (g : ℕ → ℝ → ℝ) : Prop :=
  TendstoLocallyUniformly (fun n z => ghatC (g n) (a n) z / ghatC (g n) (a n) 0)
    (fun z => Xi z / Xi 0) atTop

theorem tendstoLocallyUniformly_shift {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    (h : TendstoLocallyUniformly F f atTop) (N : ℕ) :
    TendstoLocallyUniformly (fun m => F (m + N)) f atTop := fun u hu x => by
  obtain ⟨t, ht, hev⟩ := h u hu x
  exact ⟨t, ht, (tendsto_add_atTop_nat N).eventually hev⟩

/-- **§11 item 1 ⇒ RH, with prime-side hypotheses only.** Ground states of Weil's form `Q` at
supports `2a n` whose transforms are eventually real-rooted (b) and satisfy `HypConv` (a) give
Mathlib's `RiemannHypothesis`. -/
theorem rh_of_prime_side {a : ℕ → ℝ} {g : ℕ → ℝ → ℝ} (hgs : ∀ n, IsGroundState (a n) (g n))
    (hRR : ∀ᶠ n in atTop, RealRooted (a n) (g n)) (hconv : HypConv a g) : RiemannHypothesis := by
  have hX0 := Xi_zero_ne_zero
  -- `ĝ_n(0) ≠ 0` eventually: the quotient at `0` tends to `1`, while `0/0 = 0`.
  have h0 : ∀ᶠ n in atTop, ghatC (g n) (a n) 0 ≠ 0 := by
    have hc : TendstoLocallyUniformly (fun n z => ghatC (g n) (a n) z / ghatC (g n) (a n) 0)
      (fun z => Xi z / Xi 0) atTop := hconv
    have hu := Metric.tendstoUniformlyOn_iff.1
      ((tendstoLocallyUniformly_iff_forall_isCompact.1 hc) {0} isCompact_singleton) 1 one_pos
    filter_upwards [hu] with n hn h
    have := hn 0 rfl
    simp only [div_self hX0, h, div_zero, dist_zero_right, norm_one] at this
    exact lt_irrefl _ this
  obtain ⟨N, hN⟩ := (hRR.and h0).exists_forall_of_atTop
  have hint : ∀ n, IntervalIntegrable (g n) volume (-(a n)) (a n) :=
    fun n => (probe_integrable (hgs n).1).intervalIntegrable
  have hreal : ∀ z, Xi z / Xi 0 = 0 → z.im = 0 :=
    hurwitz_real (F := fun m z => ghatC (g (m + N)) (a (m + N)) z / ghatC (g (m + N)) (a (m + N)) 0)
      (fun m => (ghatC_differentiable (hint _)).div_const _)
      (differentiable_Xi.div_const _) (tendstoLocallyUniformly_shift hconv N)
      ⟨0, by rw [div_self hX0]; exact one_ne_zero⟩
      (fun m z h => (hN (m + N) (by omega)).1 z
        ((div_eq_zero_iff.1 h).resolve_right (hN (m + N) (by omega)).2))
  intro s hz htriv _
  apply re_eq_half_of_Xi_real
  apply hreal
  rw [Xi_at_ordinate, xi_eq_zero_of_nontrivial ⟨hz, htriv⟩, zero_div]

/-- **The D-route is a special case of (a).** Hadamard factorisations, Hypothesis D below `T_D(n)`
and tails `ε → 0` give `HypConv` (Theorem 1bu(ii)). -/
theorem hypConv_of_D {a : ℕ → ℝ} {g : ℕ → ℝ → ℝ}
    {ι : ℕ → Type} {κ : Type} {w : ∀ n, ι n → ℂ} {v : κ → ℂ}
    (hF : ∀ n, HadamardW (ghatC (g n) (a n)) (w n)) (hX : HadamardW Xi v)
    {B : ℝ} (hB : ∀ n, (∑' i, ‖w n i‖) ≤ B) {t : ℕ → ℝ} (hD : ∀ n, DFamW (w n) v (t n))
    (hε : Tendsto (fun n => tailEps (w n) v (t n)) atTop (𝓝 0)) : HypConv a g := by
  choose P w' v' hw' hv' hsw hθ using fun n => pairing_of_D (hF n) hX (hD n)
  exact tendstoLocallyUniformly_of_pairing hw' hv' (fun n => (hsw n).le.trans (hB n)) hθ hε

/-- **(b) from shape.** A probe that agrees a.e. on `[−a, a]` with a nonzero member of Pólya's class
(even, concave on `(−a, a)`) is real-rooted. -/
theorem realRooted_of_polya_shape {a β : ℝ} (ha : 0 < a) (hβ : 0 ≤ β) {μ : Measure ℝ} [SFinite μ]
    (hμ : IntegrableOn (fun c => a - c) (Set.Ico 0 a) μ) (hnd : 0 < β ∨ μ (Set.Ico 0 a) ≠ 0)
    {g : ℝ → ℝ} (hg : ∀ᵐ u ∂volume, |u| ≤ a → g u = polyaFn a β μ u) : RealRooted a g := by
  have he : ghatC g a = ghatC (polyaFn a β μ) a := by
    funext z
    unfold ghatC
    refine intervalIntegral.integral_congr_ae (hg.mono fun u hu hmem => ?_)
    rw [Set.uIoc_of_le (by linarith)] at hmem
    rw [hu (abs_le.2 ⟨hmem.1.le, hmem.2⟩)]
  intro z hz
  rw [he] at hz
  exact realRooted_polya ha hβ hμ hnd z hz

end Pilot1ca

#print axioms Pilot1ca.rh_of_prime_side
#print axioms Pilot1ca.hypConv_of_D
#print axioms Pilot1ca.realRooted_of_polya_shape
