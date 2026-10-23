/-
# Round 710: the refined certificate at `L = 899/400` with `n = 300`, parts 351–354 of 534

File 91 of 135: the parts `rows22475R_351` … `rows22475R_354` of `SieveCert22475R.lean`'s certificate on
`SieveGrid22475R.grid22475R` (4 parts, 25966 tests: row 108 columns 52–58, row 108 columns 59–65, row 108 columns
66–74, row 108 columns 75–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22475R_351 : rowsJ2 108 109 52 59 ≤ 29694359876901 := by decide +kernel

theorem rows22475R_352 : rowsJ2 108 109 59 66 ≤ 6376720220614 := by decide +kernel

theorem rows22475R_353 : rowsJ2 108 109 66 75 ≤ 8893346907962 := by decide +kernel

theorem rows22475R_354 : rowsJ2 108 109 75 300 ≤ 897592246324180 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22475R_351
#print axioms SieveCert.rows22475R_354
