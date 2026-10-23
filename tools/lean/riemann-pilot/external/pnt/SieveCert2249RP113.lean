/-
# Round 710: the refined certificate at `L = 2249/1000` with `n = 300`, parts 434–437 of 503

File 113 of 127: the parts `rows2249R_434` … `rows2249R_437` of `SieveCert2249R.lean`'s certificate on
`SieveGrid2249R.grid2249R` (4 parts, 27214 tests: row 138 columns 0–42, row 138 columns 43–299, row 139 columns
0–42, row 139 columns 43–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows2249R_434 : rowsJ2 138 139 0 43 ≤ 120993519989751 := by decide +kernel

theorem rows2249R_435 : rowsJ2 138 139 43 300 ≤ 2383160230940159 := by decide +kernel

theorem rows2249R_436 : rowsJ2 139 140 0 43 ≤ 126620790620761 := by decide +kernel

theorem rows2249R_437 : rowsJ2 139 140 43 300 ≤ 2373975819255726 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2249R_434
#print axioms SieveCert.rows2249R_437
