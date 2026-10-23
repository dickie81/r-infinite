/-
# Round 631: Linnik's theorem with exponent `2285/1000`, unconditional

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Plain statement (`linnik_2285U`): there is `K` such that for every `q ≥ 1` and every `a` prime to `q` there is a prime
`p ≡ a (mod q)` with `p ≤ K·q^{2285/1000}`. No hypothesis beyond Mathlib's and PNT+'s theorems: round 623's route
(`SieveTypeIIHM.typeII_gen_hm` on the curve `gU`) at `L = 2285/1000`, with round 619's
`SieveMain.linnik_route_lt`, which takes the certificate's total less than `K`.

* `route2285U`, `routeOK2285U`: `L = 2285/1000` on the window `[40302/100000, 47464/100000]`.
* `typeII2285U`: `SieveTypeIIU2285.typeII_2285` as `TypeIIAt`.
* `SieveCert.grid2285U`, `gridOK2285U`, `total_lt_2285U` (`SieveGrid2285U.lean`, `SieveCert2285U.lean`): the grid of
  the window with `n = 250`, its total less than `K` in 252 kernel checks.
* `fits2285U`: `(40302/100000)·DEN < U1`, `U2 < (47464/100000)·DEN` and `DEN < (2285/1000)·U2`.
* `linnik_2285U`: `SieveMain.linnik_route_lt` at them.

The file imports `SieveMain.lean`, `SieveCert2285U.lean` and `SieveTypeIIU2285.lean`.
-/
import SieveMain
import SieveCert2285U
import SieveTypeIIU2285

namespace Linnik2285U

open SieveCert SieveRoute SieveQ

/-- **The unconditional route's parameters at `2285/1000`**: `L = 2285/1000` on the window
`[40302/100000, 47464/100000]`. -/
@[instance_reducible] noncomputable def route2285U : Route := ⟨2285 / 1000, 40302 / 100000, 47464 / 100000⟩

/-- `route2285U` is a route: `2 < L ≤ 5/2` and `0 < w₁ < w₂ < 1`. -/
theorem routeOK2285U : @RouteOK route2285U :=
  @RouteOK.mk route2285U (show (2 : ℝ) < 2285 / 1000 by norm_num) (show (0 : ℝ) < 40302 / 100000 by norm_num)
    (show (40302 / 100000 : ℝ) < 47464 / 100000 by norm_num) (show (47464 / 100000 : ℝ) < 1 by norm_num)
    (show (2285 / 1000 : ℝ) ≤ 5 / 2 by norm_num)

/-- **`SieveTypeIIU2285.typeII_2285` as `TypeIIAt`** at the route's parameters. -/
theorem typeII2285U : @TypeIIAt route2285U := by
  intro f0 hf0 hsupp K₀ e₁ η he₁ hη hη1
  exact SieveTypeIIU2285.typeII_2285 hf0 hsupp K₀ he₁ hη hη1

/-- `grid2285U` fits `route2285U`: `(40302/100000)·DEN < U1`, `U2 < (47464/100000)·DEN` and `DEN < (2285/1000)·U2`. -/
theorem fits2285U : @Fits route2285U grid2285U := by
  refine @Fits.mk route2285U grid2285U ?_ ?_ ?_
  · have h : (40302 * DEN : ℕ) < 100000 * ((40302 * DEN + 99999) / 100000) := by decide
    have h' : (40302 : ℝ) * DEN < 100000 * (((40302 * DEN + 99999) / 100000 : ℕ) : ℝ) := by exact_mod_cast h
    show (40302 / 100000 : ℝ) * DEN < (((40302 * DEN + 99999) / 100000 : ℕ) : ℝ)
    linarith
  · have h : 100000 * (47464 * DEN / 100000) < 47464 * DEN := by decide
    have h' : (100000 : ℝ) * ((47464 * DEN / 100000 : ℕ) : ℝ) < 47464 * DEN := by exact_mod_cast h
    show ((47464 * DEN / 100000 : ℕ) : ℝ) < 47464 / 100000 * DEN
    linarith
  · have h : 1000 * DEN < 2285 * (47464 * DEN / 100000) := by decide
    have h' : (1000 : ℝ) * DEN < 2285 * ((47464 * DEN / 100000 : ℕ) : ℝ) := by exact_mod_cast h
    show (DEN : ℝ) < 2285 / 1000 * ((47464 * DEN / 100000 : ℕ) : ℝ)
    linarith

/-- **Linnik's theorem with exponent `2285/1000`.** There is `K` such that for every `q ≥ 1` and every `a` prime to
`q` there is a prime `p ≡ a (mod q)` with `p ≤ K·q^{2285/1000}`. -/
theorem linnik_2285U : ∃ K : ℝ, ∀ (q : ℕ) [NeZero q] (a : ℕ), a.Coprime q →
    ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD q] ∧ (p : ℝ) ≤ K * (q : ℝ) ^ (2285 / 1000 : ℝ) :=
  @SieveMain.linnik_route_lt route2285U routeOK2285U grid2285U gridOK2285U fits2285U typeII2285U total_lt_2285U

end Linnik2285U

#print axioms Linnik2285U.routeOK2285U
#print axioms Linnik2285U.typeII2285U
#print axioms Linnik2285U.fits2285U
#print axioms Linnik2285U.linnik_2285U
