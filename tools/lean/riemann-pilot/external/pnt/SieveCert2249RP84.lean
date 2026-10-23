/-
# Round 710: the refined certificate at `L = 2249/1000` with `n = 300`, parts 319–322 of 503

File 84 of 127: the parts `rows2249R_319` … `rows2249R_322` of `SieveCert2249R.lean`'s certificate on
`SieveGrid2249R.grid2249R` (4 parts, 25919 tests: row 105 columns 66–74, row 105 columns 75–299, row 106 columns
0–51, row 106 columns 52–58), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows2249R_319 : rowsJ2 105 106 66 75 ≤ 7567330303751 := by decide +kernel

theorem rows2249R_320 : rowsJ2 105 106 75 300 ≤ 902667576548398 := by decide +kernel

theorem rows2249R_321 : rowsJ2 106 107 0 52 ≤ 345944600790591 := by decide +kernel

theorem rows2249R_322 : rowsJ2 106 107 52 59 ≤ 20128166603745 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2249R_319
#print axioms SieveCert.rows2249R_322
