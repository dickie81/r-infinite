/-
# Round 710: the refined certificate at `L = 2249/1000` with `n = 300`, parts 400–403 of 503

File 105 of 127: the parts `rows2249R_400` … `rows2249R_403` of `SieveCert2249R.lean`'s certificate on
`SieveGrid2249R.grid2249R` (4 parts, 25523 tests: row 125 columns 57–299, row 126 columns 0–45, row 126 columns
46–55, row 126 columns 56–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows2249R_400 : rowsJ2 125 126 57 300 ≤ 1205654816620455 := by decide +kernel

theorem rows2249R_401 : rowsJ2 126 127 0 46 ≤ 132829929947923 := by decide +kernel

theorem rows2249R_402 : rowsJ2 126 127 46 56 ≤ 54810518350807 := by decide +kernel

theorem rows2249R_403 : rowsJ2 126 127 56 300 ≤ 1377432573517814 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2249R_400
#print axioms SieveCert.rows2249R_403
