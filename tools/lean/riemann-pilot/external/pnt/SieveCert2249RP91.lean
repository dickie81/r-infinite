/-
# Round 710: the refined certificate at `L = 2249/1000` with `n = 300`, parts 345–348 of 503

File 91 of 127: the parts `rows2249R_345` … `rows2249R_348` of `SieveCert2249R.lean`'s certificate on
`SieveGrid2249R.grid2249R` (4 parts, 29354 tests: row 111 columns 0–50, row 111 columns 51–57, row 111 columns
58–65, row 111 columns 66–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
+kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid2249R.lean`.
-/
import SieveGrid2249R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid2249R

theorem rows2249R_345 : rowsJ2 111 112 0 51 ≤ 275762965925817 := by decide +kernel

theorem rows2249R_346 : rowsJ2 111 112 51 58 ≤ 36669333152598 := by decide +kernel

theorem rows2249R_347 : rowsJ2 111 112 58 66 ≤ 9257279743716 := by decide +kernel

theorem rows2249R_348 : rowsJ2 111 112 66 300 ≤ 557476091350673 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2249R_345
#print axioms SieveCert.rows2249R_348
