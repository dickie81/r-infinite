/-
# Round 621: Linnik's theorem with exponent `230/100`, unconditional

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Plain statement (`linnik_230`): there is `K` such that for every `q ≥ 1` and every `a` prime to `q` there is a prime
`p ≡ a (mod q)` with `p ≤ K·q^{230/100}`. No hypothesis beyond Mathlib's and PNT+'s theorems: the route of `SieveMain`
with the density curve `gU` of round 609 and the Type II bound of `typeII_gen_hm` (orthogonality or Halász–Montgomery
per bin, the latter from `LinnikPower.hm_duality` and `LinnikOffDiag.norm_offK_le`).

* `route230`, `routeOK230`: `L = 230/100` on the window `[3944/10000, 4780/10000]`.
* `typeII230`: `SieveTypeIIU230.typeII_230` as `TypeIIAt`.
* `SieveCert.grid230`, `gridOK230`, `total_le_230` (`SieveCert230.lean`): the grid of the window with `n = 100`, its
  total at most `0.88K` in one kernel check.
* `fits230`: the grid fits the route; `linnik_230`: `SieveMain.linnik_route` at them.

The file imports `SieveMain.lean`, `SieveCert230.lean` and `SieveTypeIIU230.lean`.
-/
import SieveMain
import SieveCert230
import SieveTypeIIU230

namespace Linnik230

open SieveCert SieveRoute SieveQ

/-- **The unconditional route's parameters**: `L = 230/100` on the window `[3944/10000, 4780/10000]`. -/
@[instance_reducible] noncomputable def route230 : Route := ⟨230 / 100, 3944 / 10000, 4780 / 10000⟩

/-- `route230` is a route: `2 < L ≤ 5/2` and `0 < w₁ < w₂ < 1`. -/
theorem routeOK230 : @RouteOK route230 :=
  @RouteOK.mk route230 (show (2 : ℝ) < 230 / 100 by norm_num) (show (0 : ℝ) < 3944 / 10000 by norm_num)
    (show (3944 / 10000 : ℝ) < 4780 / 10000 by norm_num) (show (4780 / 10000 : ℝ) < 1 by norm_num)
    (show (230 / 100 : ℝ) ≤ 5 / 2 by norm_num)

/-- **`SieveTypeIIU230.typeII_230` as `TypeIIAt`** at the unconditional route's parameters. -/
theorem typeII230 : @TypeIIAt route230 := by
  intro f0 hf0 hsupp K₀ e₁ η he₁ hη hη1
  exact SieveTypeIIU230.typeII_230 hf0 hsupp K₀ he₁ hη hη1

/-- `grid230` fits `route230`: `(3944/10000)·DEN < U1`, `U2 < (4780/10000)·DEN` and `DEN < (230/100)·U2`. -/
theorem fits230 : @Fits route230 grid230 := by
  refine @Fits.mk route230 grid230 ?_ ?_ ?_
  · have h : (3944 * DEN : ℕ) < 10000 * ((3944 * DEN + 9999) / 10000) := by decide
    have h' : (3944 : ℝ) * DEN < 10000 * (((3944 * DEN + 9999) / 10000 : ℕ) : ℝ) := by exact_mod_cast h
    show (3944 / 10000 : ℝ) * DEN < (((3944 * DEN + 9999) / 10000 : ℕ) : ℝ)
    linarith
  · have h : 10000 * (4780 * DEN / 10000) < 4780 * DEN := by decide
    have h' : (10000 : ℝ) * ((4780 * DEN / 10000 : ℕ) : ℝ) < 4780 * DEN := by exact_mod_cast h
    show ((4780 * DEN / 10000 : ℕ) : ℝ) < 4780 / 10000 * DEN
    linarith
  · have h : 100 * DEN < 230 * (4780 * DEN / 10000) := by decide
    have h' : (100 : ℝ) * DEN < 230 * ((4780 * DEN / 10000 : ℕ) : ℝ) := by exact_mod_cast h
    show (DEN : ℝ) < 230 / 100 * ((4780 * DEN / 10000 : ℕ) : ℝ)
    linarith

/-- **Linnik's theorem with exponent `230/100`.** There is `K` such that for every `q ≥ 1` and every `a` prime to
`q` there is a prime `p ≡ a (mod q)` with `p ≤ K·q^{230/100}`. -/
theorem linnik_230 : ∃ K : ℝ, ∀ (q : ℕ) [NeZero q] (a : ℕ), a.Coprime q →
    ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD q] ∧ (p : ℝ) ≤ K * (q : ℝ) ^ (230 / 100 : ℝ) :=
  @SieveMain.linnik_route route230 routeOK230 grid230 gridOK230 fits230 typeII230 total_le_230

end Linnik230

#print axioms Linnik230.routeOK230
#print axioms Linnik230.typeII230
#print axioms Linnik230.fits230
#print axioms Linnik230.linnik_230
