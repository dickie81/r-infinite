/-
# Round 710: the refined certificate at `L = 2249/1000` with `n = 300`, parts 357–360 of 503

File 94 of 127: the parts `rows2249R_357` … `rows2249R_360` of `SieveCert2249R.lean`'s certificate on
`SieveGrid2249R.grid2249R` (4 parts, 27690 tests: row 114 columns 0–49, row 114 columns 50–56, row 114 columns
57–65, row 114 columns 66–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows2249R_357 : rowsJ2 114 115 0 50 ≤ 236331799910220 := by decide +kernel

theorem rows2249R_358 : rowsJ2 114 115 50 57 ≤ 43788152592311 := by decide +kernel

theorem rows2249R_359 : rowsJ2 114 115 57 66 ≤ 12255098279940 := by decide +kernel

theorem rows2249R_360 : rowsJ2 114 115 66 300 ≤ 336155097548550 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2249R_357
#print axioms SieveCert.rows2249R_360
