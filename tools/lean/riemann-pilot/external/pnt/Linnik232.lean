/-
# Round 609: Linnik's theorem with exponent `232/100`, unconditional

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Plain statement (`linnik_232`): there is `K` such that for every `q ≥ 1` and every `a` prime to `q` there is a prime
`p ≡ a (mod q)` with `p ≤ K·q^{232/100}`. It has no hypothesis: every input is a theorem of the stack.

`SieveMain.linnik_route` takes a route (`L` and the Type II window `[w₁, w₂]`), a grid of the certificate, the fit
between them, the Type II estimate on the window and the certificate's total. Here they are:

* `route232`, `routeOK232`: `L = 232/100` on the window `[4045/10000, 4825/10000]`.
* `typeII232`: `SieveTypeIIU232.typeII_232` as `TypeIIAt`.
* `SieveCert.grid232`, `gridOK232`, `total_le_232` (`SieveCert232.lean`): the grid of the window with `n = 150`
  cells, and its total at most `0.88`.
* `fits232`: `(4045/10000)·DEN < U1`, `U2 < (4825/10000)·DEN` and `DEN < (232/100)·U2`.

The file imports `SieveMain.lean`, `SieveCert232.lean` and `SieveTypeIIU232.lean`.
-/
import SieveMain
import SieveCert232
import SieveTypeIIU232

namespace Linnik232

open SieveCert SieveRoute SieveQ

/-- **The unconditional route's parameters**: `L = 232/100` on the window `[4045/10000, 4825/10000]`. -/
@[instance_reducible] noncomputable def route232 : Route := ⟨232 / 100, 4045 / 10000, 4825 / 10000⟩

theorem routeOK232 : @RouteOK route232 :=
  @RouteOK.mk route232 (show (2 : ℝ) < 232 / 100 by norm_num) (show (0 : ℝ) < 4045 / 10000 by norm_num)
    (show (4045 / 10000 : ℝ) < 4825 / 10000 by norm_num) (show (4825 / 10000 : ℝ) < 1 by norm_num)
    (show (232 / 100 : ℝ) ≤ 5 / 2 by norm_num)

/-- **`SieveTypeIIU232.typeII_232` as `TypeIIAt`** at the unconditional route's parameters. -/
theorem typeII232 : @TypeIIAt route232 := by
  intro f0 hf0 hsupp K₀ e₁ η he₁ hη hη1
  exact SieveTypeIIU232.typeII_232 hf0 hsupp K₀ he₁ hη hη1

/-- `grid232` fits `route232`: `(4045/10000)·DEN < U1`, `U2 < (4825/10000)·DEN` and `DEN < (232/100)·U2`. -/
theorem fits232 : @Fits route232 grid232 := by
  refine @Fits.mk route232 grid232 ?_ ?_ ?_
  · have h : (4045 * DEN : ℕ) < 10000 * ((4045 * DEN + 9999) / 10000) := by decide
    have h' : (4045 : ℝ) * DEN < 10000 * (((4045 * DEN + 9999) / 10000 : ℕ) : ℝ) := by exact_mod_cast h
    show (4045 / 10000 : ℝ) * DEN < (((4045 * DEN + 9999) / 10000 : ℕ) : ℝ)
    linarith
  · have h : 10000 * (4825 * DEN / 10000) < 4825 * DEN := by decide
    have h' : (10000 : ℝ) * ((4825 * DEN / 10000 : ℕ) : ℝ) < 4825 * DEN := by exact_mod_cast h
    show ((4825 * DEN / 10000 : ℕ) : ℝ) < 4825 / 10000 * DEN
    linarith
  · have h : 100 * DEN < 232 * (4825 * DEN / 10000) := by decide
    have h' : (100 : ℝ) * DEN < 232 * ((4825 * DEN / 10000 : ℕ) : ℝ) := by exact_mod_cast h
    show (DEN : ℝ) < 232 / 100 * ((4825 * DEN / 10000 : ℕ) : ℝ)
    linarith

/-- **Linnik's theorem with exponent `232/100`.** There is `K` such that for every `q ≥ 1` and every `a` prime to
`q` there is a prime `p ≡ a (mod q)` with `p ≤ K·q^{232/100}`. -/
theorem linnik_232 : ∃ K : ℝ, ∀ (q : ℕ) [NeZero q] (a : ℕ), a.Coprime q →
    ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD q] ∧ (p : ℝ) ≤ K * (q : ℝ) ^ (232 / 100 : ℝ) :=
  @SieveMain.linnik_route route232 routeOK232 grid232 gridOK232 fits232 typeII232 total_le_232

end Linnik232

#print axioms Linnik232.routeOK232
#print axioms Linnik232.typeII232
#print axioms Linnik232.fits232
#print axioms Linnik232.linnik_232
