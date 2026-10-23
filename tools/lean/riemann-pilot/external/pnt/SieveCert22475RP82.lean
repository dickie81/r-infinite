/-
# Round 710: the refined certificate at `L = 899/400` with `n = 300`, parts 318–321 of 534

File 82 of 135: the parts `rows22475R_318` … `rows22475R_321` of `SieveCert22475R.lean`'s certificate on
`SieveGrid22475R.grid22475R` (4 parts, 23706 tests: row 101 columns 73–85, row 101 columns 86–299, row 102 columns
0–52, row 102 columns 53–59), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22475R_318 : rowsJ2 101 102 73 86 ≤ 534620873158324 := by decide +kernel

theorem rows22475R_319 : rowsJ2 101 102 86 300 ≤ 788283416222484 := by decide +kernel

theorem rows22475R_320 : rowsJ2 102 103 0 53 ≤ 497694717463490 := by decide +kernel

theorem rows22475R_321 : rowsJ2 102 103 53 60 ≤ 6130900986283 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22475R_318
#print axioms SieveCert.rows22475R_321
