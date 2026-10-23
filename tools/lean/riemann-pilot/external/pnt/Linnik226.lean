/-
# Round 614: Linnik's theorem with exponent `226/100`, under Chen–Gupta–Li's estimate and Petrow–Young's bound

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Plain statement (`linnik_226`): if `LinnikCGL.CGLDensity` and `LinnikWeyl.PYWeyl` hold, there is `K` such that for every
`q ≥ 1` and every `a` prime to `q` there is a prime `p ≡ a (mod q)` with `p ≤ K·q^{226/100}`.

`SieveMain.linnik_route` takes a route (`L` and the Type II window `[w₁, w₂]`), a grid of the certificate, the fit
between them, the Type II estimate on the window and the certificate's total. Here they are:

* `route226`, `routeOK226`: `L = 226/100` on the window `[4075/10000, 4835/10000]`.
* `typeII226`: `SieveTypeIIU226.typeII_226`, under `CGLDensity` and `PYWeyl`, as `TypeIIAt`.
* `SieveCert.grid226`, `gridOK226`, `total_le_226` (`SieveCert226.lean`): the grid of the window with `n = 200`
  cells, and its total at most `0.88`.
* `fits226`: `(4075/10000)·DEN < U1`, `U2 < (4835/10000)·DEN` and `DEN < (226/100)·U2`.

The file imports `SieveMain.lean`, `SieveCert226.lean` and `SieveTypeIIU226.lean`.
-/
import SieveMain
import SieveCert226
import SieveTypeIIU226

namespace Linnik226

open SieveCert SieveRoute SieveQ

/-- **The Weyl-conditional route's parameters at `226/100`**: `L = 226/100` on the window `[4075/10000, 4835/10000]`. -/
@[instance_reducible] noncomputable def route226 : Route := ⟨226 / 100, 4075 / 10000, 4835 / 10000⟩

theorem routeOK226 : @RouteOK route226 :=
  @RouteOK.mk route226 (show (2 : ℝ) < 226 / 100 by norm_num) (show (0 : ℝ) < 4075 / 10000 by norm_num)
    (show (4075 / 10000 : ℝ) < 4835 / 10000 by norm_num) (show (4835 / 10000 : ℝ) < 1 by norm_num)
    (show (226 / 100 : ℝ) ≤ 5 / 2 by norm_num)

/-- **`SieveTypeIIU226.typeII_226` as `TypeIIAt`** at the route's parameters, under `CGLDensity` and `PYWeyl`. -/
theorem typeII226 (hCGL : LinnikCGL.CGLDensity) (hPY : LinnikWeyl.PYWeyl) : @TypeIIAt route226 := by
  intro f0 hf0 hsupp K₀ e₁ η he₁ hη hη1
  exact SieveTypeIIU226.typeII_226 hCGL hPY hf0 hsupp K₀ he₁ hη hη1

/-- `grid226` fits `route226`: `(4075/10000)·DEN < U1`, `U2 < (4835/10000)·DEN` and `DEN < (226/100)·U2`. -/
theorem fits226 : @Fits route226 grid226 := by
  refine @Fits.mk route226 grid226 ?_ ?_ ?_
  · have h : (4075 * DEN : ℕ) < 10000 * ((4075 * DEN + 9999) / 10000) := by decide
    have h' : (4075 : ℝ) * DEN < 10000 * (((4075 * DEN + 9999) / 10000 : ℕ) : ℝ) := by exact_mod_cast h
    show (4075 / 10000 : ℝ) * DEN < (((4075 * DEN + 9999) / 10000 : ℕ) : ℝ)
    linarith
  · have h : 10000 * (4835 * DEN / 10000) < 4835 * DEN := by decide
    have h' : (10000 : ℝ) * ((4835 * DEN / 10000 : ℕ) : ℝ) < 4835 * DEN := by exact_mod_cast h
    show ((4835 * DEN / 10000 : ℕ) : ℝ) < 4835 / 10000 * DEN
    linarith
  · have h : 100 * DEN < 226 * (4835 * DEN / 10000) := by decide
    have h' : (100 : ℝ) * DEN < 226 * ((4835 * DEN / 10000 : ℕ) : ℝ) := by exact_mod_cast h
    show (DEN : ℝ) < 226 / 100 * ((4835 * DEN / 10000 : ℕ) : ℝ)
    linarith

/-- **Linnik's theorem with exponent `226/100`, under `CGLDensity` and `PYWeyl`.** There is `K` such that for every
`q ≥ 1` and every `a` prime to `q` there is a prime `p ≡ a (mod q)` with `p ≤ K·q^{226/100}`. -/
theorem linnik_226 (hCGL : LinnikCGL.CGLDensity) (hPY : LinnikWeyl.PYWeyl) :
    ∃ K : ℝ, ∀ (q : ℕ) [NeZero q] (a : ℕ), a.Coprime q →
    ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD q] ∧ (p : ℝ) ≤ K * (q : ℝ) ^ (226 / 100 : ℝ) :=
  @SieveMain.linnik_route route226 routeOK226 grid226 gridOK226 fits226 (typeII226 hCGL hPY) total_le_226

end Linnik226

#print axioms Linnik226.routeOK226
#print axioms Linnik226.typeII226
#print axioms Linnik226.fits226
#print axioms Linnik226.linnik_226
