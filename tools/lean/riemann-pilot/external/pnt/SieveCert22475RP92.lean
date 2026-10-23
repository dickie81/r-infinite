/-
# Round 710: the refined certificate at `L = 899/400` with `n = 300`, parts 355–358 of 534

File 92 of 135: the parts `rows22475R_355` … `rows22475R_358` of `SieveCert22475R.lean`'s certificate on
`SieveGrid22475R.grid22475R` (4 parts, 29930 tests: row 109 columns 0–51, row 109 columns 52–57, row 109 columns
58–64, row 109 columns 65–73), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22475R_355 : rowsJ2 109 110 0 52 ≤ 368163400287822 := by decide +kernel

theorem rows22475R_356 : rowsJ2 109 110 52 58 ≤ 29648004687198 := by decide +kernel

theorem rows22475R_357 : rowsJ2 109 110 58 65 ≤ 11430509970410 := by decide +kernel

theorem rows22475R_358 : rowsJ2 109 110 65 74 ≤ 5345174371262 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22475R_355
#print axioms SieveCert.rows22475R_358
