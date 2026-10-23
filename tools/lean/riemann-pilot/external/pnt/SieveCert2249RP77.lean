/-
# Round 710: the refined certificate at `L = 2249/1000` with `n = 300`, parts 293–296 of 503

File 77 of 127: the parts `rows2249R_293` … `rows2249R_296` of `SieveCert2249R.lean`'s certificate on
`SieveGrid2249R.grid2249R` (4 parts, 29513 tests: row 100 columns 60–65, row 100 columns 66–72, row 100 columns
73–299, row 101 columns 0–52), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows2249R_293 : rowsJ2 100 101 60 66 ≤ 0 := by decide +kernel

theorem rows2249R_294 : rowsJ2 100 101 66 73 ≤ 1139040025819 := by decide +kernel

theorem rows2249R_295 : rowsJ2 100 101 73 300 ≤ 1189501941842592 := by decide +kernel

theorem rows2249R_296 : rowsJ2 101 102 0 53 ≤ 432808064108006 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2249R_293
#print axioms SieveCert.rows2249R_296
