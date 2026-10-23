/-
# Round 710: the refined certificate at `L = 899/400` with `n = 300`, parts 205–208 of 534

File 53 of 135: the parts `rows22475R_205` … `rows22475R_208` of `SieveCert22475R.lean`'s certificate on
`SieveGrid22475R.grid22475R` (4 parts, 23715 tests: row 84 columns 68–72, row 84 columns 73–77, row 84 columns
78–83, row 84 columns 84–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22475R_205 : rowsJ2 84 85 68 73 ≤ 4940688543052 := by decide +kernel

theorem rows22475R_206 : rowsJ2 84 85 73 78 ≤ 2296405436851 := by decide +kernel

theorem rows22475R_207 : rowsJ2 84 85 78 84 ≤ 12848503239745 := by decide +kernel

theorem rows22475R_208 : rowsJ2 84 85 84 300 ≤ 5031198550850 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22475R_205
#print axioms SieveCert.rows22475R_208
