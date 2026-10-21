/-
# Round 625: Linnik's theorem with exponent `9/4`, under Chen–Gupta–Li's estimate alone

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Plain statement (`linnik_225c`): if `LinnikCGL.CGLDensity` holds, there is `K` such that for every `q ≥ 1` and every
`a` prime to `q` there is a prime `p ≡ a (mod q)` with `p ≤ K·q^{9/4}`: round 622's route (`SieveTypeIIHM.typeII_gen_hm`
on the curve `g7c`) at `L = 9/4`, with round 619's `SieveMain.linnik_route_lt`, which takes the certificate's total
less than `K`.

* `route225C`, `routeOK225C`: `L = 9/4` on the window `[41191/100000, 48127/100000]`.
* `typeII225c`: `SieveTypeIIU225C.typeII_225c`, under `CGLDensity`, as `TypeIIAt`.
* `SieveCert.grid225C`, `gridOK225C`, `total_lt_225C` (`SieveGrid225C.lean`, `SieveCert225C.lean`): the grid of the
  window with `n = 400`, its total less than `K` in 1374 kernel checks.
* `fits225C`: `(41191/100000)·DEN < U1`, `U2 < (48127/100000)·DEN` and `DEN < (9/4)·U2`.
* `linnik_225c`: `SieveMain.linnik_route_lt` at them.

The file imports `SieveMain.lean`, `SieveCert225C.lean` and `SieveTypeIIU225C.lean`.
-/
import SieveMain
import SieveCert225C
import SieveTypeIIU225C

namespace Linnik225C

open SieveCert SieveRoute SieveQ

/-- **The route's parameters at `9/4`**: `L = 9/4` on the window `[41191/100000, 48127/100000]`. -/
@[instance_reducible] noncomputable def route225C : Route := ⟨9 / 4, 41191 / 100000, 48127 / 100000⟩

/-- `route225C` is a route: `2 < L ≤ 5/2` and `0 < w₁ < w₂ < 1`. -/
theorem routeOK225C : @RouteOK route225C :=
  @RouteOK.mk route225C (show (2 : ℝ) < 9 / 4 by norm_num) (show (0 : ℝ) < 41191 / 100000 by norm_num)
    (show (41191 / 100000 : ℝ) < 48127 / 100000 by norm_num) (show (48127 / 100000 : ℝ) < 1 by norm_num)
    (show (9 / 4 : ℝ) ≤ 5 / 2 by norm_num)

/-- **`SieveTypeIIU225C.typeII_225c` as `TypeIIAt`** at the route's parameters, under `CGLDensity` (`hCGL`). -/
theorem typeII225c (hCGL : LinnikCGL.CGLDensity) : @TypeIIAt route225C := by
  intro f0 hf0 hsupp K₀ e₁ η he₁ hη hη1
  exact SieveTypeIIU225C.typeII_225c hCGL hf0 hsupp K₀ he₁ hη hη1

/-- `grid225C` fits `route225C`: `(41191/100000)·DEN < U1`, `U2 < (48127/100000)·DEN` and `DEN < (9/4)·U2`. -/
theorem fits225C : @Fits route225C grid225C := by
  refine @Fits.mk route225C grid225C ?_ ?_ ?_
  · have h : (41191 * DEN : ℕ) < 100000 * ((41191 * DEN + 99999) / 100000) := by decide
    have h' : (41191 : ℝ) * DEN < 100000 * (((41191 * DEN + 99999) / 100000 : ℕ) : ℝ) := by exact_mod_cast h
    show (41191 / 100000 : ℝ) * DEN < (((41191 * DEN + 99999) / 100000 : ℕ) : ℝ)
    linarith
  · have h : 100000 * (48127 * DEN / 100000) < 48127 * DEN := by decide
    have h' : (100000 : ℝ) * ((48127 * DEN / 100000 : ℕ) : ℝ) < 48127 * DEN := by exact_mod_cast h
    show ((48127 * DEN / 100000 : ℕ) : ℝ) < 48127 / 100000 * DEN
    linarith
  · have h : 4 * DEN < 9 * (48127 * DEN / 100000) := by decide
    have h' : (4 : ℝ) * DEN < 9 * ((48127 * DEN / 100000 : ℕ) : ℝ) := by exact_mod_cast h
    show (DEN : ℝ) < 9 / 4 * ((48127 * DEN / 100000 : ℕ) : ℝ)
    linarith

/-- **Linnik's theorem with exponent `9/4`, under `CGLDensity`** (`hCGL`). There is `K` such that for every `q ≥ 1`
and every `a` prime to `q` there is a prime `p ≡ a (mod q)` with `p ≤ K·q^{9/4}`. -/
theorem linnik_225c (hCGL : LinnikCGL.CGLDensity) : ∃ K : ℝ, ∀ (q : ℕ) [NeZero q] (a : ℕ), a.Coprime q →
    ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD q] ∧ (p : ℝ) ≤ K * (q : ℝ) ^ (9 / 4 : ℝ) :=
  @SieveMain.linnik_route_lt route225C routeOK225C grid225C gridOK225C fits225C (typeII225c hCGL) total_lt_225C

end Linnik225C

#print axioms Linnik225C.routeOK225C
#print axioms Linnik225C.typeII225c
#print axioms Linnik225C.fits225C
#print axioms Linnik225C.linnik_225c
