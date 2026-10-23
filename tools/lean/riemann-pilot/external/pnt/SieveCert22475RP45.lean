/-
# Round 710: the refined certificate at `L = 899/400` with `n = 300`, parts 175–178 of 534

File 45 of 135: the parts `rows22475R_175` … `rows22475R_178` of `SieveCert22475R.lean`'s certificate on
`SieveGrid22475R.grid22475R` (4 parts, 26139 tests: row 79 columns 73–77, row 79 columns 78–299, row 80 columns
0–34, row 80 columns 35–60), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22475R_175 : rowsJ2 79 80 73 78 ≤ 9996622147108 := by decide +kernel

theorem rows22475R_176 : rowsJ2 79 80 78 300 ≤ 2783627202145 := by decide +kernel

theorem rows22475R_177 : rowsJ2 80 81 0 35 ≤ 513019599238071 := by decide +kernel

theorem rows22475R_178 : rowsJ2 80 81 35 61 ≤ 743127028642583 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22475R_175
#print axioms SieveCert.rows22475R_178
