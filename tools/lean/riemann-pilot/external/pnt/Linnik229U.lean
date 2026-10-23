/-
# Round 623: Linnik's theorem with exponent `229/100`, unconditional

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Plain statement (`linnik_229U`): there is `K` such that for every `q ≥ 1` and every `a` prime to `q` there is a prime
`p ≡ a (mod q)` with `p ≤ K·q^{229/100}`. No hypothesis beyond Mathlib's and PNT+'s theorems: round 621's route
(`SieveTypeIIHM.typeII_gen_hm` on the curve `gU`) one hundredth lower, with round 619's `SieveMain.linnik_route_lt`,
which takes the certificate's total less than `K`. Round 607's `Linnik229.linnik_229` is the same exponent under
`CGLDensity`.

* `route229U`, `routeOK229U`: `L = 229/100` on the window `[40011/100000, 47579/100000]`.
* `typeII229U`: `SieveTypeIIU229.typeII_229` as `TypeIIAt`.
* `SieveCert.grid229U`, `gridOK229U`, `total_lt_229U` (`SieveGrid229U.lean`, `SieveCert229U.lean`): the grid of the
  window with `n = 150`, its total less than `K` in 21 kernel checks.
* `fits229U`: `(40011/100000)·DEN < U1`, `U2 < (47579/100000)·DEN` and `DEN < (229/100)·U2`.
* `linnik_229U`: `SieveMain.linnik_route_lt` at them.

The file imports `SieveMain.lean`, `SieveCert229U.lean` and `SieveTypeIIU229.lean`.
-/
import SieveMain
import SieveCert229U
import SieveTypeIIU229

namespace Linnik229U

open SieveCert SieveRoute SieveQ

/-- **The unconditional route's parameters at `229/100`**: `L = 229/100` on the window
`[40011/100000, 47579/100000]`. -/
@[instance_reducible] noncomputable def route229U : Route := ⟨229 / 100, 40011 / 100000, 47579 / 100000⟩

/-- `route229U` is a route: `2 < L ≤ 5/2` and `0 < w₁ < w₂ < 1`. -/
theorem routeOK229U : @RouteOK route229U :=
  @RouteOK.mk route229U (show (2 : ℝ) < 229 / 100 by norm_num) (show (0 : ℝ) < 40011 / 100000 by norm_num)
    (show (40011 / 100000 : ℝ) < 47579 / 100000 by norm_num) (show (47579 / 100000 : ℝ) < 1 by norm_num)
    (show (229 / 100 : ℝ) ≤ 5 / 2 by norm_num)

/-- **`SieveTypeIIU229.typeII_229` as `TypeIIAt`** at the route's parameters. -/
theorem typeII229U : @TypeIIAt route229U := by
  intro f0 hf0 hsupp K₀ e₁ η he₁ hη hη1
  exact SieveTypeIIU229.typeII_229 hf0 hsupp K₀ he₁ hη hη1

/-- `grid229U` fits `route229U`: `(40011/100000)·DEN < U1`, `U2 < (47579/100000)·DEN` and `DEN < (229/100)·U2`. -/
theorem fits229U : @Fits route229U grid229U := by
  refine @Fits.mk route229U grid229U ?_ ?_ ?_
  · have h : (40011 * DEN : ℕ) < 100000 * ((40011 * DEN + 99999) / 100000) := by decide
    have h' : (40011 : ℝ) * DEN < 100000 * (((40011 * DEN + 99999) / 100000 : ℕ) : ℝ) := by exact_mod_cast h
    show (40011 / 100000 : ℝ) * DEN < (((40011 * DEN + 99999) / 100000 : ℕ) : ℝ)
    linarith
  · have h : 100000 * (47579 * DEN / 100000) < 47579 * DEN := by decide
    have h' : (100000 : ℝ) * ((47579 * DEN / 100000 : ℕ) : ℝ) < 47579 * DEN := by exact_mod_cast h
    show ((47579 * DEN / 100000 : ℕ) : ℝ) < 47579 / 100000 * DEN
    linarith
  · have h : 100 * DEN < 229 * (47579 * DEN / 100000) := by decide
    have h' : (100 : ℝ) * DEN < 229 * ((47579 * DEN / 100000 : ℕ) : ℝ) := by exact_mod_cast h
    show (DEN : ℝ) < 229 / 100 * ((47579 * DEN / 100000 : ℕ) : ℝ)
    linarith

/-- **Linnik's theorem with exponent `229/100`.** There is `K` such that for every `q ≥ 1` and every `a` prime to
`q` there is a prime `p ≡ a (mod q)` with `p ≤ K·q^{229/100}`. -/
theorem linnik_229U : ∃ K : ℝ, ∀ (q : ℕ) [NeZero q] (a : ℕ), a.Coprime q →
    ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD q] ∧ (p : ℝ) ≤ K * (q : ℝ) ^ (229 / 100 : ℝ) :=
  @SieveMain.linnik_route_lt route229U routeOK229U grid229U gridOK229U fits229U typeII229U total_lt_229U

end Linnik229U

#print axioms Linnik229U.routeOK229U
#print axioms Linnik229U.typeII229U
#print axioms Linnik229U.fits229U
#print axioms Linnik229U.linnik_229U
