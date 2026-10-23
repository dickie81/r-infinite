/-
# Round 710: the refined certificate at `L = 899/400` with `n = 300`, parts 311–314 of 534

File 80 of 135: the parts `rows22475R_311` … `rows22475R_314` of `SieveCert22475R.lean`'s certificate on
`SieveGrid22475R.grid22475R` (4 parts, 24218 tests: row 100 columns 66–72, row 100 columns 73–81, row 100 columns
82–299, row 101 columns 0–52), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22475R_311 : rowsJ2 100 101 66 73 ≤ 1039511936593 := by decide +kernel

theorem rows22475R_312 : rowsJ2 100 101 73 82 ≤ 48170640572092 := by decide +kernel

theorem rows22475R_313 : rowsJ2 100 101 82 300 ≤ 1403364511855534 := by decide +kernel

theorem rows22475R_314 : rowsJ2 101 102 0 53 ≤ 517301290867849 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22475R_311
#print axioms SieveCert.rows22475R_314
