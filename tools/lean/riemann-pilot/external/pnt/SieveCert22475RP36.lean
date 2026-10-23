/-
# Round 710: the refined certificate at `L = 899/400` with `n = 300`, parts 142–145 of 534

File 36 of 135: the parts `rows22475R_142` … `rows22475R_145` of `SieveCert22475R.lean`'s certificate on
`SieveGrid22475R.grid22475R` (4 parts, 24247 tests: row 73 columns 68–72, row 73 columns 73–299, row 74 columns
0–34, row 74 columns 35–50), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22475R_142 : rowsJ2 73 74 68 73 ≤ 29713465146448 := by decide +kernel

theorem rows22475R_143 : rowsJ2 73 74 73 300 ≤ 6241520761700 := by decide +kernel

theorem rows22475R_144 : rowsJ2 74 75 0 35 ≤ 552762747561278 := by decide +kernel

theorem rows22475R_145 : rowsJ2 74 75 35 51 ≤ 780981920763010 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22475R_142
#print axioms SieveCert.rows22475R_145
