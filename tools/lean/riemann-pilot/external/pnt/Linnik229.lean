/-
# Round 607: Linnik's theorem with exponent `229/100`, under the density estimate of Chen, Gupta and Li

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Plain statement (`linnik_229`): if `LinnikCGL.CGLDensity` holds, there is `K` such that for every `q ≥ 1` and every
`a` prime to `q` there is a prime `p ≡ a (mod q)` with `p ≤ K·q^{229/100}`.

`SieveMain.linnik_route` takes a route (`L` and the Type II window `[w₁, w₂]`), a grid of the certificate, the fit
between them, the Type II estimate on the window and the certificate's total. Here they are:

* `route229`, `routeOK229`: `L = 229/100` on the window `[4123/10000, 4902/10000]`.
* `typeII229`: `SieveTypeII73.typeII_73`, under `CGLDensity`, as `TypeIIAt`.
* `SieveCert.grid229`, `gridOK229`, `total_le_229` (`SieveCert229.lean`): the grid of the window with `n = 100`
  cells, and its total at most `0.88`.
* `fits229`: `(4123/10000)·DEN < U1`, `U2 < (4902/10000)·DEN` and `DEN < (229/100)·U2`.

The file imports `SieveMain.lean`, `SieveCert229.lean` and `SieveTypeII73.lean`.
-/
import SieveMain
import SieveCert229
import SieveTypeII73

namespace Linnik229

open SieveCert SieveRoute SieveQ

/-- **The second goal's parameters**: `L = 229/100` on the window `[4123/10000, 4902/10000]`. -/
@[instance_reducible] noncomputable def route229 : Route := ⟨229 / 100, 4123 / 10000, 4902 / 10000⟩

theorem routeOK229 : @RouteOK route229 :=
  @RouteOK.mk route229 (show (2 : ℝ) < 229 / 100 by norm_num) (show (0 : ℝ) < 4123 / 10000 by norm_num)
    (show (4123 / 10000 : ℝ) < 4902 / 10000 by norm_num) (show (4902 / 10000 : ℝ) < 1 by norm_num)
    (show (229 / 100 : ℝ) ≤ 5 / 2 by norm_num)

/-- **`SieveTypeII73.typeII_73` as `TypeIIAt`** at the second goal's parameters, under `CGLDensity`. -/
theorem typeII229 (hCGL : LinnikCGL.CGLDensity) : @TypeIIAt route229 := by
  intro f0 hf0 hsupp K₀ e₁ η he₁ hη hη1
  exact SieveTypeII73.typeII_73 hCGL hf0 hsupp K₀ he₁ hη hη1

/-- `grid229` fits `route229`: `(4123/10000)·DEN < U1`, `U2 < (4902/10000)·DEN` and `DEN < (229/100)·U2`. -/
theorem fits229 : @Fits route229 grid229 := by
  refine @Fits.mk route229 grid229 ?_ ?_ ?_
  · have h : (4123 * DEN : ℕ) < 10000 * ((4123 * DEN + 9999) / 10000) := by decide
    have h' : (4123 : ℝ) * DEN < 10000 * (((4123 * DEN + 9999) / 10000 : ℕ) : ℝ) := by exact_mod_cast h
    show (4123 / 10000 : ℝ) * DEN < (((4123 * DEN + 9999) / 10000 : ℕ) : ℝ)
    linarith
  · have h : 10000 * (4902 * DEN / 10000) < 4902 * DEN := by decide
    have h' : (10000 : ℝ) * ((4902 * DEN / 10000 : ℕ) : ℝ) < 4902 * DEN := by exact_mod_cast h
    show ((4902 * DEN / 10000 : ℕ) : ℝ) < 4902 / 10000 * DEN
    linarith
  · have h : 100 * DEN < 229 * (4902 * DEN / 10000) := by decide
    have h' : (100 : ℝ) * DEN < 229 * ((4902 * DEN / 10000 : ℕ) : ℝ) := by exact_mod_cast h
    show (DEN : ℝ) < 229 / 100 * ((4902 * DEN / 10000 : ℕ) : ℝ)
    linarith

/-- **Linnik's theorem with exponent `229/100`, under `CGLDensity`.** There is `K` such that for every `q ≥ 1` and
every `a` prime to `q` there is a prime `p ≡ a (mod q)` with `p ≤ K·q^{229/100}`. -/
theorem linnik_229 (hCGL : LinnikCGL.CGLDensity) : ∃ K : ℝ, ∀ (q : ℕ) [NeZero q] (a : ℕ), a.Coprime q →
    ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD q] ∧ (p : ℝ) ≤ K * (q : ℝ) ^ (229 / 100 : ℝ) :=
  @SieveMain.linnik_route route229 routeOK229 grid229 gridOK229 fits229 (typeII229 hCGL) total_le_229

end Linnik229

#print axioms Linnik229.routeOK229
#print axioms Linnik229.typeII229
#print axioms Linnik229.fits229
#print axioms Linnik229.linnik_229
