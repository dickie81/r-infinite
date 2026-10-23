/-
# Round 710: the refined certificate at `L = 899/400` with `n = 300`, parts 150–153 of 534

File 38 of 135: the parts `rows22475R_150` … `rows22475R_153` of `SieveCert22475R.lean`'s certificate on
`SieveGrid22475R.grid22475R` (4 parts, 27552 tests: row 75 columns 35–53, row 75 columns 54–67, row 75 columns
68–72, row 75 columns 73–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22475R_150 : rowsJ2 75 76 35 54 ≤ 840422829018949 := by decide +kernel

theorem rows22475R_151 : rowsJ2 75 76 54 68 ≤ 192583421036888 := by decide +kernel

theorem rows22475R_152 : rowsJ2 75 76 68 73 ≤ 20095494895757 := by decide +kernel

theorem rows22475R_153 : rowsJ2 75 76 73 300 ≤ 13468836742670 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22475R_150
#print axioms SieveCert.rows22475R_153
