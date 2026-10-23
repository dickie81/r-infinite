/-
# Round 710: the refined certificate at `L = 899/400` with `n = 300`, parts 404–407 of 534

File 105 of 135: the parts `rows22475R_404` … `rows22475R_407` of `SieveCert22475R.lean`'s certificate on
`SieveGrid22475R.grid22475R` (4 parts, 27065 tests: row 120 columns 56–65, row 120 columns 66–299, row 121 columns
0–48, row 121 columns 49–56), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22475R_404 : rowsJ2 120 121 56 66 ≤ 14728967622359 := by decide +kernel

theorem rows22475R_405 : rowsJ2 120 121 66 300 ≤ 523839373950310 := by decide +kernel

theorem rows22475R_406 : rowsJ2 121 122 0 49 ≤ 211856370091009 := by decide +kernel

theorem rows22475R_407 : rowsJ2 121 122 49 57 ≤ 58507177172702 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22475R_404
#print axioms SieveCert.rows22475R_407
