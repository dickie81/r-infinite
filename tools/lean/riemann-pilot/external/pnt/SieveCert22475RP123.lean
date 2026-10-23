/-
# Round 710: the refined certificate at `L = 899/400` with `n = 300`, parts 477–480 of 534

File 123 of 135: the parts `rows22475R_477` … `rows22475R_480` of `SieveCert22475R.lean`'s certificate on
`SieveGrid22475R.grid22475R` (4 parts, 22739 tests: row 146 columns 0–40, row 146 columns 41–299, row 147 columns
0–40, row 147 columns 41–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22475R_477 : rowsJ2 146 147 0 41 ≤ 151962657962964 := by decide +kernel

theorem rows22475R_478 : rowsJ2 146 147 41 300 ≤ 2528167185642797 := by decide +kernel

theorem rows22475R_479 : rowsJ2 147 148 0 41 ≤ 159501730244736 := by decide +kernel

theorem rows22475R_480 : rowsJ2 147 148 41 300 ≤ 2531961641431765 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22475R_477
#print axioms SieveCert.rows22475R_480
