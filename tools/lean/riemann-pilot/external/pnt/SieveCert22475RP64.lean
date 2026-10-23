/-
# Round 710: the refined certificate at `L = 899/400` with `n = 300`, parts 247–250 of 534

File 64 of 135: the parts `rows22475R_247` … `rows22475R_250` of `SieveCert22475R.lean`'s certificate on
`SieveGrid22475R.grid22475R` (4 parts, 24221 tests: row 90 columns 67–71, row 90 columns 72–77, row 90 columns
78–84, row 90 columns 85–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22475R_247 : rowsJ2 90 91 67 72 ≤ 158857239824 := by decide +kernel

theorem rows22475R_248 : rowsJ2 90 91 72 78 ≤ 3567775085843 := by decide +kernel

theorem rows22475R_249 : rowsJ2 90 91 78 85 ≤ 36153355241910 := by decide +kernel

theorem rows22475R_250 : rowsJ2 90 91 85 300 ≤ 612065920541213 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22475R_247
#print axioms SieveCert.rows22475R_250
