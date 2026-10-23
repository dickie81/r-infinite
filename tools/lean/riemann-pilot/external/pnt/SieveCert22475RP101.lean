/-
# Round 710: the refined certificate at `L = 899/400` with `n = 300`, parts 388–391 of 534

File 101 of 135: the parts `rows22475R_388` … `rows22475R_391` of `SieveCert22475R.lean`'s certificate on
`SieveGrid22475R.grid22475R` (4 parts, 28558 tests: row 116 columns 57–65, row 116 columns 66–299, row 117 columns
0–49, row 117 columns 50–56), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22475R_388 : rowsJ2 116 117 57 66 ≤ 17586706029113 := by decide +kernel

theorem rows22475R_389 : rowsJ2 116 117 66 300 ≤ 444447776833090 := by decide +kernel

theorem rows22475R_390 : rowsJ2 117 118 0 50 ≤ 253985235232248 := by decide +kernel

theorem rows22475R_391 : rowsJ2 117 118 50 57 ≤ 53087901320231 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22475R_388
#print axioms SieveCert.rows22475R_391
