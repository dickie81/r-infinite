/-
# Round 710: Linnik's theorem with exponent `899/400`, under the refined certificate at `n = 300`

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Plain statements (`linnik_22475r_of`, `linnik_22475r`): there is `K` such that for every `q ≥ 1` and every `a` prime to
`q` there is a prime `p ≡ a (mod q)` with `p ≤ K·q^{899/400}`; the first under `LinnikCGL.CGLDensity`, the second
with no hypothesis. The route at `L = 899/400` on the window `[41335/100000, 48069/100000]` of
`frontier/linnik/route_limits.jsonl`'s rows for `g7c` (`route22475C`, with its Type II estimate
`SieveTypeIIU22475C.typeII_22475c`), on its grid with `n = 300` (`SieveCert.grid22475R`), whose refined certificate's
total is less than `K` (`SieveCert.total2_lt_22475R`), with `SieveMain2.linnik_route_lt2`. The certificate of
`SieveCertDefs.lean` totals more than `K` on that grid, and on each grid that `route_limits.jsonl` replays at this
window, up to `n = 800`.

* `route22475C`, `routeOK22475C`: `L = 899/400` on `[41335/100000, 48069/100000]`; `2 < L ≤ 5/2` and
  `0 < w₁ < w₂ < 1`.
* `typeII22475c`: `SieveTypeIIU22475C.typeII_22475c`, under `CGLDensity`, as `TypeIIAt`.
* `fits22475R`: `grid22475R` fits `route22475C`: `(41335/100000)·DEN < U1`, `U2 < (48069/100000)·DEN` and
  `DEN < (899/400)·U2`.
* `linnik_22475r_of`: `SieveMain2.linnik_route_lt2` at them, under `CGLDensity`.
* `linnik_22475r`: `linnik_22475r_of` at `LinnikCGLDensity.cglDensity`.

The file imports `SieveMain2.lean`, `SieveCert22475R.lean`, `SieveTypeIIU22475C.lean` and `LinnikCGLDensity.lean`.
-/
import SieveMain2
import SieveCert22475R
import SieveTypeIIU22475C
import LinnikCGLDensity

namespace Linnik22475R

open SieveCert SieveRoute SieveQ

/-- **The route's parameters at `899/400`**: `L = 899/400` on the window `[41335/100000, 48069/100000]`. -/
@[instance_reducible] noncomputable def route22475C : Route := ⟨899 / 400, 41335 / 100000, 48069 / 100000⟩

/-- `route22475C` is a route: `2 < L ≤ 5/2` and `0 < w₁ < w₂ < 1`. -/
theorem routeOK22475C : @RouteOK route22475C :=
  @RouteOK.mk route22475C (show (2 : ℝ) < 899 / 400 by norm_num) (show (0 : ℝ) < 41335 / 100000 by norm_num)
    (show (41335 / 100000 : ℝ) < 48069 / 100000 by norm_num) (show (48069 / 100000 : ℝ) < 1 by norm_num)
    (show (899 / 400 : ℝ) ≤ 5 / 2 by norm_num)

/-- **`SieveTypeIIU22475C.typeII_22475c` as `TypeIIAt`** at the route's parameters, under `CGLDensity` (`hCGL`). -/
theorem typeII22475c (hCGL : LinnikCGL.CGLDensity) : @TypeIIAt route22475C := by
  intro f0 hf0 hsupp K₀ e₁ η he₁ hη hη1
  exact SieveTypeIIU22475C.typeII_22475c hCGL hf0 hsupp K₀ he₁ hη hη1

/-- `grid22475R` fits `route22475C`: `(41335/100000)·DEN < U1`, `U2 < (48069/100000)·DEN` and `DEN < (899/400)·U2`. -/
theorem fits22475R : @Fits route22475C grid22475R := by
  refine @Fits.mk route22475C grid22475R ?_ ?_ ?_
  · have h : (41335 * DEN : ℕ) < 100000 * ((41335 * DEN + 99999) / 100000) := by decide
    have h' : (41335 : ℝ) * DEN < 100000 * (((41335 * DEN + 99999) / 100000 : ℕ) : ℝ) := by exact_mod_cast h
    show (41335 / 100000 : ℝ) * DEN < (((41335 * DEN + 99999) / 100000 : ℕ) : ℝ)
    linarith
  · have h : 100000 * (48069 * DEN / 100000) < 48069 * DEN := by decide
    have h' : (100000 : ℝ) * ((48069 * DEN / 100000 : ℕ) : ℝ) < 48069 * DEN := by exact_mod_cast h
    show ((48069 * DEN / 100000 : ℕ) : ℝ) < 48069 / 100000 * DEN
    linarith
  · have h : 400 * DEN < 899 * (48069 * DEN / 100000) := by decide
    have h' : (400 : ℝ) * DEN < 899 * ((48069 * DEN / 100000 : ℕ) : ℝ) := by exact_mod_cast h
    show (DEN : ℝ) < 899 / 400 * ((48069 * DEN / 100000 : ℕ) : ℝ)
    linarith

/-- **Linnik's theorem with exponent `899/400`, under `CGLDensity` (`hCGL`), by the refined certificate at
`n = 300`.** There is `K` such that for every `q ≥ 1` and every `a` prime to `q` there is a prime `p ≡ a (mod q)` with
`p ≤ K·q^{899/400}`. -/
theorem linnik_22475r_of (hCGL : LinnikCGL.CGLDensity) : ∃ K : ℝ, ∀ (q : ℕ) [NeZero q] (a : ℕ), a.Coprime q →
    ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD q] ∧ (p : ℝ) ≤ K * (q : ℝ) ^ (899 / 400 : ℝ) :=
  @SieveMain2.linnik_route_lt2 route22475C routeOK22475C grid22475R gridOK22475R fits22475R (typeII22475c hCGL)
    total2_lt_22475R

/-- **Linnik's theorem with exponent `899/400`, by the refined certificate at `n = 300`**, `linnik_22475r_of` at
`LinnikCGLDensity.cglDensity`: there is `K` such that for every `q ≥ 1` and every `a` prime to `q` there is a prime
`p ≡ a (mod q)` with `p ≤ K·q^{899/400}`. -/
theorem linnik_22475r : ∃ K : ℝ, ∀ (q : ℕ) [NeZero q] (a : ℕ), a.Coprime q →
    ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD q] ∧ (p : ℝ) ≤ K * (q : ℝ) ^ (899 / 400 : ℝ) :=
  linnik_22475r_of LinnikCGLDensity.cglDensity

end Linnik22475R

#print axioms Linnik22475R.routeOK22475C
#print axioms Linnik22475R.typeII22475c
#print axioms Linnik22475R.fits22475R
#print axioms Linnik22475R.linnik_22475r_of
#print axioms Linnik22475R.linnik_22475r
