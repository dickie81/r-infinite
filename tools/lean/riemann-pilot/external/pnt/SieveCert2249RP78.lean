/-
# Round 710: the refined certificate at `L = 2249/1000` with `n = 300`, parts 297–300 of 503

File 78 of 127: the parts `rows2249R_297` … `rows2249R_300` of `SieveCert2249R.lean`'s certificate on
`SieveGrid2249R.grid2249R` (4 parts, 28563 tests: row 101 columns 53–59, row 101 columns 60–65, row 101 columns
66–73, row 101 columns 74–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows2249R_297 : rowsJ2 101 102 53 60 ≤ 2511106398123 := by decide +kernel

theorem rows2249R_298 : rowsJ2 101 102 60 66 ≤ 0 := by decide +kernel

theorem rows2249R_299 : rowsJ2 101 102 66 74 ≤ 2916740850205 := by decide +kernel

theorem rows2249R_300 : rowsJ2 101 102 74 300 ≤ 1173736747520476 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2249R_297
#print axioms SieveCert.rows2249R_300
