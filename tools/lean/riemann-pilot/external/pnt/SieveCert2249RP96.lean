/-
# Round 710: the refined certificate at `L = 2249/1000` with `n = 300`, parts 365–368 of 503

File 96 of 127: the parts `rows2249R_365` … `rows2249R_368` of `SieveCert2249R.lean`'s certificate on
`SieveGrid2249R.grid2249R` (4 parts, 26497 tests: row 116 columns 0–49, row 116 columns 50–57, row 116 columns
58–68, row 116 columns 69–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows2249R_365 : rowsJ2 116 117 0 50 ≤ 218771078887217 := by decide +kernel

theorem rows2249R_366 : rowsJ2 116 117 50 58 ≤ 47159160784629 := by decide +kernel

theorem rows2249R_367 : rowsJ2 116 117 58 69 ≤ 7006802516837 := by decide +kernel

theorem rows2249R_368 : rowsJ2 116 117 69 300 ≤ 223895669623166 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2249R_365
#print axioms SieveCert.rows2249R_368
