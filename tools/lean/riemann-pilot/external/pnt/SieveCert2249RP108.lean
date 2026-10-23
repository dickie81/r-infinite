/-
# Round 710: the refined certificate at `L = 2249/1000` with `n = 300`, parts 413–416 of 503

File 108 of 127: the parts `rows2249R_413` … `rows2249R_416` of `SieveCert2249R.lean`'s certificate on
`SieveGrid2249R.grid2249R` (4 parts, 25712 tests: row 130 columns 0–44, row 130 columns 45–55, row 130 columns
56–299, row 131 columns 0–44), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows2249R_413 : rowsJ2 130 131 0 45 ≤ 120574269296748 := by decide +kernel

theorem rows2249R_414 : rowsJ2 130 131 45 56 ≤ 49050014840348 := by decide +kernel

theorem rows2249R_415 : rowsJ2 130 131 56 300 ≤ 1982096261245673 := by decide +kernel

theorem rows2249R_416 : rowsJ2 131 132 0 45 ≤ 122778997796465 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2249R_413
#print axioms SieveCert.rows2249R_416
