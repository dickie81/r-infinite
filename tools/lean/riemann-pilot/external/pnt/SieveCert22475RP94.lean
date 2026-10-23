/-
# Round 710: the refined certificate at `L = 899/400` with `n = 300`, parts 363–366 of 534

File 94 of 135: the parts `rows22475R_363` … `rows22475R_366` of `SieveCert22475R.lean`'s certificate on
`SieveGrid22475R.grid22475R` (4 parts, 24950 tests: row 110 columns 65–73, row 110 columns 74–299, row 111 columns
0–50, row 111 columns 51–57), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
+kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22475R.lean`.
-/
import SieveGrid22475R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22475R

theorem rows22475R_363 : rowsJ2 110 111 65 74 ≤ 6057889900254 := by decide +kernel

theorem rows22475R_364 : rowsJ2 110 111 74 300 ≤ 780172003764292 := by decide +kernel

theorem rows22475R_365 : rowsJ2 111 112 0 51 ≤ 333395008649815 := by decide +kernel

theorem rows22475R_366 : rowsJ2 111 112 51 58 ≤ 40457271253147 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22475R_363
#print axioms SieveCert.rows22475R_366
