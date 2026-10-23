/-
# Round 710: the refined certificate at `L = 899/400` with `n = 300`, parts 339–342 of 534

File 88 of 135: the parts `rows22475R_339` … `rows22475R_342` of `SieveCert22475R.lean`'s certificate on
`SieveGrid22475R.grid22475R` (4 parts, 28051 tests: row 105 columns 73–299, row 106 columns 0–51, row 106 columns
52–58, row 106 columns 59–64), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22475R_339 : rowsJ2 105 106 73 300 ≤ 1046390803057333 := by decide +kernel

theorem rows22475R_340 : rowsJ2 106 107 0 52 ≤ 419029483001509 := by decide +kernel

theorem rows22475R_341 : rowsJ2 106 107 52 59 ≤ 22465078355135 := by decide +kernel

theorem rows22475R_342 : rowsJ2 106 107 59 65 ≤ 3070880814082 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22475R_339
#print axioms SieveCert.rows22475R_342
