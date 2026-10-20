/-
# Round 612: Linnik's theorem with exponent `227/100`, under Chen–Gupta–Li's estimate and Petrow–Young's bound

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Plain statement (`linnik_227`): if `LinnikCGL.CGLDensity` and `LinnikWeyl.PYWeyl` hold, there is `K` such that for every
`q ≥ 1` and every `a` prime to `q` there is a prime `p ≡ a (mod q)` with `p ≤ K·q^{227/100}`.

`SieveMain.linnik_route` takes a route (`L` and the Type II window `[w₁, w₂]`), a grid of the certificate, the fit
between them, the Type II estimate on the window and the certificate's total. Here they are:

* `route227`, `routeOK227`: `L = 227/100` on the window `[4048/10000, 4858/10000]`.
* `typeII227`: `SieveTypeIIU227.typeII_227`, under `CGLDensity` and `PYWeyl`, as `TypeIIAt`.
* `SieveCert.grid227`, `gridOK227`, `total_le_227` (`SieveCert227.lean`): the grid of the window with `n = 100`
  cells, and its total at most `0.88`.
* `fits227`: `(4048/10000)·DEN < U1`, `U2 < (4858/10000)·DEN` and `DEN < (227/100)·U2`.

The file imports `SieveMain.lean`, `SieveCert227.lean` and `SieveTypeIIU227.lean`.
-/
import SieveMain
import SieveCert227
import SieveTypeIIU227

namespace Linnik227

open SieveCert SieveRoute SieveQ

/-- **The Weyl-conditional route's parameters**: `L = 227/100` on the window `[4048/10000, 4858/10000]`. -/
@[instance_reducible] noncomputable def route227 : Route := ⟨227 / 100, 4048 / 10000, 4858 / 10000⟩

theorem routeOK227 : @RouteOK route227 :=
  @RouteOK.mk route227 (show (2 : ℝ) < 227 / 100 by norm_num) (show (0 : ℝ) < 4048 / 10000 by norm_num)
    (show (4048 / 10000 : ℝ) < 4858 / 10000 by norm_num) (show (4858 / 10000 : ℝ) < 1 by norm_num)
    (show (227 / 100 : ℝ) ≤ 5 / 2 by norm_num)

/-- **`SieveTypeIIU227.typeII_227` as `TypeIIAt`** at the route's parameters, under `CGLDensity` and `PYWeyl`. -/
theorem typeII227 (hCGL : LinnikCGL.CGLDensity) (hPY : LinnikWeyl.PYWeyl) : @TypeIIAt route227 := by
  intro f0 hf0 hsupp K₀ e₁ η he₁ hη hη1
  exact SieveTypeIIU227.typeII_227 hCGL hPY hf0 hsupp K₀ he₁ hη hη1

/-- `grid227` fits `route227`: `(4048/10000)·DEN < U1`, `U2 < (4858/10000)·DEN` and `DEN < (227/100)·U2`. -/
theorem fits227 : @Fits route227 grid227 := by
  refine @Fits.mk route227 grid227 ?_ ?_ ?_
  · have h : (4048 * DEN : ℕ) < 10000 * ((4048 * DEN + 9999) / 10000) := by decide
    have h' : (4048 : ℝ) * DEN < 10000 * (((4048 * DEN + 9999) / 10000 : ℕ) : ℝ) := by exact_mod_cast h
    show (4048 / 10000 : ℝ) * DEN < (((4048 * DEN + 9999) / 10000 : ℕ) : ℝ)
    linarith
  · have h : 10000 * (4858 * DEN / 10000) < 4858 * DEN := by decide
    have h' : (10000 : ℝ) * ((4858 * DEN / 10000 : ℕ) : ℝ) < 4858 * DEN := by exact_mod_cast h
    show ((4858 * DEN / 10000 : ℕ) : ℝ) < 4858 / 10000 * DEN
    linarith
  · have h : 100 * DEN < 227 * (4858 * DEN / 10000) := by decide
    have h' : (100 : ℝ) * DEN < 227 * ((4858 * DEN / 10000 : ℕ) : ℝ) := by exact_mod_cast h
    show (DEN : ℝ) < 227 / 100 * ((4858 * DEN / 10000 : ℕ) : ℝ)
    linarith

/-- **Linnik's theorem with exponent `227/100`, under `CGLDensity` and `PYWeyl`.** There is `K` such that for every
`q ≥ 1` and every `a` prime to `q` there is a prime `p ≡ a (mod q)` with `p ≤ K·q^{227/100}`. -/
theorem linnik_227 (hCGL : LinnikCGL.CGLDensity) (hPY : LinnikWeyl.PYWeyl) :
    ∃ K : ℝ, ∀ (q : ℕ) [NeZero q] (a : ℕ), a.Coprime q →
    ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD q] ∧ (p : ℝ) ≤ K * (q : ℝ) ^ (227 / 100 : ℝ) :=
  @SieveMain.linnik_route route227 routeOK227 grid227 gridOK227 fits227 (typeII227 hCGL hPY) total_le_227

end Linnik227

#print axioms Linnik227.routeOK227
#print axioms Linnik227.typeII227
#print axioms Linnik227.fits227
#print axioms Linnik227.linnik_227
