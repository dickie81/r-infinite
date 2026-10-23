/-
# Round 709: Linnik's theorem with exponent `9/4`, under the refined certificate at `n = 200`

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Plain statements (`linnik_225r_of`, `linnik_225r`): there is `K` such that for every `q ≥ 1` and every `a` prime to
`q` there is a prime `p ≡ a (mod q)` with `p ≤ K·q^{9/4}`; the first under `LinnikCGL.CGLDensity`, the second with no
hypothesis. Round 625's route at `L = 9/4` (`Linnik225C.route225C`, with its Type II estimate
`Linnik225C.typeII225c`), on round 705's grid of the same window with `n = 200` (`SieveCert.grid225R`), whose refined
certificate's total is less than `K` (`SieveCert.total2_lt_225R`), with `SieveMain2.linnik_route_lt2`. Round 625's
theorem took the certificate of `SieveCertDefs.lean` on the grid with `n = 400`, in 1374 kernel checks; the
refinement (`SieveCert2Defs.lean`: on a dropped candidate cell of depth 2, the kept parts' shares come off the cell's
bound) takes half the cells a side, in 117.

* `fits225R`: `grid225R` fits `route225C`: `(41191/100000)·DEN < U1`, `U2 < (48127/100000)·DEN` and
  `DEN < (9/4)·U2`.
* `linnik_225r_of`: `SieveMain2.linnik_route_lt2` at them, under `CGLDensity`.
* `linnik_225r`: `linnik_225r_of` at `LinnikCGLDensity.cglDensity`.

The file imports `SieveMain2.lean`, `SieveCert225R.lean`, `Linnik225C.lean` and `LinnikCGLDensity.lean`.
-/
import SieveMain2
import SieveCert225R
import Linnik225C
import LinnikCGLDensity

namespace Linnik225R

open SieveCert SieveRoute SieveQ Linnik225C

/-- `grid225R` fits `route225C`: `(41191/100000)·DEN < U1`, `U2 < (48127/100000)·DEN` and `DEN < (9/4)·U2`. -/
theorem fits225R : @Fits route225C grid225R := by
  refine @Fits.mk route225C grid225R ?_ ?_ ?_
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

/-- **Linnik's theorem with exponent `9/4`, under `CGLDensity` (`hCGL`), by the refined certificate at `n = 200`.**
There is `K` such that for every `q ≥ 1` and every `a` prime to `q` there is a prime `p ≡ a (mod q)` with
`p ≤ K·q^{9/4}`. -/
theorem linnik_225r_of (hCGL : LinnikCGL.CGLDensity) : ∃ K : ℝ, ∀ (q : ℕ) [NeZero q] (a : ℕ), a.Coprime q →
    ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD q] ∧ (p : ℝ) ≤ K * (q : ℝ) ^ (9 / 4 : ℝ) :=
  @SieveMain2.linnik_route_lt2 route225C routeOK225C grid225R gridOK225R fits225R (typeII225c hCGL) total2_lt_225R

/-- **Linnik's theorem with exponent `9/4`, by the refined certificate at `n = 200`**, `linnik_225r_of` at
`LinnikCGLDensity.cglDensity`: there is `K` such that for every `q ≥ 1` and every `a` prime to `q` there is a prime
`p ≡ a (mod q)` with `p ≤ K·q^{9/4}`. -/
theorem linnik_225r : ∃ K : ℝ, ∀ (q : ℕ) [NeZero q] (a : ℕ), a.Coprime q →
    ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD q] ∧ (p : ℝ) ≤ K * (q : ℝ) ^ (9 / 4 : ℝ) :=
  linnik_225r_of LinnikCGLDensity.cglDensity

end Linnik225R

#print axioms Linnik225R.fits225R
#print axioms Linnik225R.linnik_225r_of
#print axioms Linnik225R.linnik_225r
