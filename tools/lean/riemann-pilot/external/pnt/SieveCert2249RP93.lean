/-
# Round 710: the refined certificate at `L = 2249/1000` with `n = 300`, parts 353–356 of 503

File 93 of 127: the parts `rows2249R_353` … `rows2249R_356` of `SieveCert2249R.lean`'s certificate on
`SieveGrid2249R.grid2249R` (4 parts, 28130 tests: row 113 columns 0–49, row 113 columns 50–56, row 113 columns
57–65, row 113 columns 66–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows2249R_353 : rowsJ2 113 114 0 50 ≤ 247566733414171 := by decide +kernel

theorem rows2249R_354 : rowsJ2 113 114 50 57 ≤ 42866380981076 := by decide +kernel

theorem rows2249R_355 : rowsJ2 113 114 57 66 ≤ 12950023636827 := by decide +kernel

theorem rows2249R_356 : rowsJ2 113 114 66 300 ≤ 444467176289013 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2249R_353
#print axioms SieveCert.rows2249R_356
