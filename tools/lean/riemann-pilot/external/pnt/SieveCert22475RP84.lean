/-
# Round 710: the refined certificate at `L = 899/400` with `n = 300`, parts 325–327 of 534

File 84 of 135: the parts `rows22475R_325` … `rows22475R_327` of `SieveCert22475R.lean`'s certificate on
`SieveGrid22475R.grid22475R` (3 parts, 22888 tests: row 103 columns 0–52, row 103 columns 53–59, row 103 columns
60–65), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
(`Elab.async false`).

The file imports `SieveGrid22475R.lean`.
-/
import SieveGrid22475R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22475R

theorem rows22475R_325 : rowsJ2 103 104 0 53 ≤ 476723324978081 := by decide +kernel

theorem rows22475R_326 : rowsJ2 103 104 53 60 ≤ 9298773128246 := by decide +kernel

theorem rows22475R_327 : rowsJ2 103 104 60 66 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22475R_325
#print axioms SieveCert.rows22475R_327
