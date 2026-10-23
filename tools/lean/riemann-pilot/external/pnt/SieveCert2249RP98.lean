/-
# Round 710: the refined certificate at `L = 2249/1000` with `n = 300`, parts 373–376 of 503

File 98 of 127: the parts `rows2249R_373` … `rows2249R_376` of `SieveCert2249R.lean`'s certificate on
`SieveGrid2249R.grid2249R` (4 parts, 25331 tests: row 118 columns 0–48, row 118 columns 49–56, row 118 columns
57–67, row 118 columns 68–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows2249R_373 : rowsJ2 118 119 0 49 ≤ 195473289520587 := by decide +kernel

theorem rows2249R_374 : rowsJ2 118 119 49 57 ≤ 50751054318501 := by decide +kernel

theorem rows2249R_375 : rowsJ2 118 119 57 68 ≤ 7276055299148 := by decide +kernel

theorem rows2249R_376 : rowsJ2 118 119 68 300 ≤ 112452998191463 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2249R_373
#print axioms SieveCert.rows2249R_376
