/-
# Round 710: the refined certificate at `L = 2249/1000` with `n = 300`, parts 361–364 of 503

File 95 of 127: the parts `rows2249R_361` … `rows2249R_364` of `SieveCert2249R.lean`'s certificate on
`SieveGrid2249R.grid2249R` (4 parts, 26936 tests: row 115 columns 0–49, row 115 columns 50–56, row 115 columns
57–66, row 115 columns 67–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows2249R_361 : rowsJ2 115 116 0 50 ≤ 228145577185126 := by decide +kernel

theorem rows2249R_362 : rowsJ2 115 116 50 57 ≤ 44643248416491 := by decide +kernel

theorem rows2249R_363 : rowsJ2 115 116 57 67 ≤ 11340180464096 := by decide +kernel

theorem rows2249R_364 : rowsJ2 115 116 67 300 ≤ 332477618626123 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2249R_361
#print axioms SieveCert.rows2249R_364
