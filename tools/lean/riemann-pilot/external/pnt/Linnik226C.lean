/-
# Round 622: Linnik's theorem with exponent `226/100` under Chen–Gupta–Li's estimate alone

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Plain statement (`linnik_226c`): if `LinnikCGL.CGLDensity` holds, there is `K` such that for every `q ≥ 1` and every
`a` prime to `q` there is a prime `p ≡ a (mod q)` with `p ≤ K·q^{226/100}`. Round 614's `Linnik226.linnik_226` needed
`LinnikWeyl.PYWeyl` as well; here the Type II estimate is round 621's `typeII_gen_hm` on the curve `g7c`
(`SieveTypeIIU226C.typeII_226c`), on the same window and the same certificate (`SieveCert.total_le_226`).

* `typeII226c`: `SieveTypeIIU226C.typeII_226c`, under `CGLDensity`, as `TypeIIAt` at `Linnik226.route226`.
* `linnik_226c`: `SieveMain.linnik_route` at `route226` and `grid226` (`routeOK226`, `fits226`, `typeII226c`,
  `total_le_226`).

The file imports `Linnik226.lean` and `SieveTypeIIU226C.lean`.
-/
import Linnik226
import SieveTypeIIU226C

namespace Linnik226C

open SieveCert SieveRoute SieveQ Linnik226

/-- **`SieveTypeIIU226C.typeII_226c` as `TypeIIAt`** at `route226`, under `CGLDensity` (`hCGL`). -/
theorem typeII226c (hCGL : LinnikCGL.CGLDensity) : @TypeIIAt route226 := by
  intro f0 hf0 hsupp K₀ e₁ η he₁ hη hη1
  exact SieveTypeIIU226C.typeII_226c hCGL hf0 hsupp K₀ he₁ hη hη1

/-- **Linnik's theorem with exponent `226/100` under `CGLDensity`** (`hCGL`). There is `K` such that for every `q ≥ 1`
and every `a` prime to `q` there is a prime `p ≡ a (mod q)` with `p ≤ K·q^{226/100}`. -/
theorem linnik_226c (hCGL : LinnikCGL.CGLDensity) :
    ∃ K : ℝ, ∀ (q : ℕ) [NeZero q] (a : ℕ), a.Coprime q →
    ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD q] ∧ (p : ℝ) ≤ K * (q : ℝ) ^ (226 / 100 : ℝ) :=
  @SieveMain.linnik_route route226 routeOK226 grid226 gridOK226 fits226 (typeII226c hCGL) total_le_226

end Linnik226C

#print axioms Linnik226C.typeII226c
#print axioms Linnik226C.linnik_226c
