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

`rh_of_prime_side` (HurwitzCross.lean): (a) + (b) for ground states of Weil's form at supports `2a n`
gives Mathlib's `RiemannHypothesis`. Nothing else is assumed: `ĝ_n(0) ≠ 0` eventually follows from (a) at `z = 0`,
and `Ξ(0) ≠ 0` is `Xi_zero_ne_zero`.

`hypConv_of_D`: the old route is a special case. D with vanishing tails implies (a) (1bu(ii)). So
the open problem is exactly (a) and (b), and D is one sufficient condition for (a), a
zero-dependent one.

`realRooted_of_ae_concaveOn` (`Concave.lean`): (b) holds at any support where the ground state is
a.e. concave on its window. -/

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

/-- Convergence of the normalised transforms at `0` forces `ĝ_n(0) ≠ 0` eventually: the quotient
at `0` tends to `1`, while `0/0 = 0`. -/
theorem eventually_ghatC_zero_ne {a : ℕ → ℝ} {g : ℕ → ℝ → ℝ} {U : Set ℂ} (hU : (0 : ℂ) ∈ U)
    (h : TendstoLocallyUniformlyOn (fun n z => ghatC (g n) (a n) z / ghatC (g n) (a n) 0)
      (fun z => Xi z / Xi 0) atTop U) : ∀ᶠ n in atTop, ghatC (g n) (a n) 0 ≠ 0 := by
  have ht := h.tendsto_at hU
  simp only [div_self Xi_zero_ne_zero] at ht
  filter_upwards [ht.eventually_ne one_ne_zero] with n hn h0
  rw [h0, div_zero] at hn; exact hn rfl

theorem HypConv.eventually_ne {a : ℕ → ℝ} {g : ℕ → ℝ → ℝ} (h : HypConv a g) :
    ∀ᶠ n in atTop, ghatC (g n) (a n) 0 ≠ 0 :=
  eventually_ghatC_zero_ne (Set.mem_univ 0) (tendstoLocallyUniformlyOn_univ.2 h)

/-- **The D-route is a special case of (a).** Hadamard factorisations, Hypothesis D below `T_D(n)`
and tails `ε → 0` give `HypConv` (Theorem 1bu(ii)). -/
theorem hypConv_of_D {a : ℕ → ℝ} {g : ℕ → ℝ → ℝ}
    {ι : ℕ → Type} {κ : Type} {w : ∀ n, ι n → ℂ} {v : κ → ℂ}
    (hF : ∀ n, HadamardW (ghatC (g n) (a n)) (w n)) (hX : HadamardW Xi v)
    {B : ℝ} (hB : ∀ n, (∑' i, ‖w n i‖) ≤ B) {t : ℕ → ℝ} (hD : ∀ n, DFamW (w n) v (t n))
    (hε : Tendsto (fun n => tailEps (w n) v (t n)) atTop (𝓝 0)) : HypConv a g := by
  choose P w' v' hw' hv' hsw hθ using fun n => pairing_of_D (hF n) hX (hD n)
  exact tendstoLocallyUniformly_of_pairing hw' hv' (fun n => (hsw n).le.trans (hB n)) hθ hε

end Pilot1ca

#print axioms Pilot1ca.eventually_ghatC_zero_ne
#print axioms Pilot1ca.hypConv_of_D
