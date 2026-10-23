/-
# Round 710: the refined certificate at `L = 899/400` with `n = 300`, parts 212–215 of 534

File 55 of 135: the parts `rows22475R_212` … `rows22475R_215` of `SieveCert22475R.lean`'s certificate on
`SieveGrid22475R.grid22475R` (4 parts, 24300 tests: row 85 columns 68–72, row 85 columns 73–77, row 85 columns
78–83, row 85 columns 84–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22475R_212 : rowsJ2 85 86 68 73 ≤ 3544153051859 := by decide +kernel

theorem rows22475R_213 : rowsJ2 85 86 73 78 ≤ 1636739002943 := by decide +kernel

theorem rows22475R_214 : rowsJ2 85 86 78 84 ≤ 14731358118676 := by decide +kernel

theorem rows22475R_215 : rowsJ2 85 86 84 300 ≤ 12384532581737 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22475R_212
#print axioms SieveCert.rows22475R_215
