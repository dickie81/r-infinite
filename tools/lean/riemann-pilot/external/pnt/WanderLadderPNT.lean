/-
# Rungs 1 and 2 of the wander ladder (round 191)

Built against PrimeNumberTheoremAnd (Kontorovich, Tao et al.) at commit
650d31264be65f4cd6e70c45d8b25d86d482a761, toolchain v4.33.1. See `external/pnt/README.md`.

* `rung1`: `ψ(x) − x = o(x)` — the prime number theorem (their `WeakPNT''`, Wiener–Ikehara route).
* `rung2`: `ψ(x) − x = O(x·e^{−c√log x})` for some `c > 0` — de la Vallée Poussin (their `StrongPNT`).
* `wander_below_any_eps`: rung 1 gives `|ψ(x) − x| ≤ ε·x` eventually, for every `ε > 0`
  (rung 0 of round 190 had `ε = 2/5`).

`ψ` is Mathlib's `Chebyshev.psi` throughout (their `ChebyshevPsi` is an abbreviation for it).
-/
import PrimeNumberTheoremAnd.StrongPNT
import PrimeNumberTheoremAnd.Consequences

open Filter Asymptotics Real

namespace WanderLadder

/-- **Rung 1 (prime number theorem):** `ψ(x) − x = o(x)`. -/
theorem rung1 : (fun x : ℝ => Chebyshev.psi x - x) =o[atTop] (fun x : ℝ => x) :=
  WeakPNT''

/-- **Rung 2 (de la Vallée Poussin):** `ψ(x) − x = O(x·exp(−c·√log x))` for some `c > 0`. -/
theorem rung2 : ∃ c > 0, (fun x : ℝ => Chebyshev.psi x - x) =O[atTop]
    (fun x : ℝ => x * Real.exp (-c * Real.log x ^ ((1 : ℝ) / 2))) :=
  StrongPNT

/-- Rung 1 squeezes the relative wander below any `ε` (rung 0 had `ε = 2/5`). -/
theorem wander_below_any_eps (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, |Chebyshev.psi x - x| ≤ ε * x := by
  have h := rung1.bound hε
  filter_upwards [h, eventually_ge_atTop 0] with x hx hx0
  simpa [Real.norm_eq_abs, abs_of_nonneg hx0] using hx

end WanderLadder

#print axioms WanderLadder.rung1
#print axioms WanderLadder.rung2
#print axioms WanderLadder.wander_below_any_eps
