/-
# Round 710: the refined certificate at `L = 899/400` with `n = 300`, parts 367–370 of 534

File 95 of 135: the parts `rows22475R_367` … `rows22475R_370` of `SieveCert22475R.lean`'s certificate on
`SieveGrid22475R.grid22475R` (4 parts, 24156 tests: row 111 columns 58–64, row 111 columns 65–74, row 111 columns
75–299, row 112 columns 0–50), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22475R_367 : rowsJ2 111 112 58 65 ≤ 14004017400721 := by decide +kernel

theorem rows22475R_368 : rowsJ2 111 112 65 75 ≤ 11496996958346 := by decide +kernel

theorem rows22475R_369 : rowsJ2 111 112 75 300 ≤ 664093527070874 := by decide +kernel

theorem rows22475R_370 : rowsJ2 112 113 0 51 ≤ 320294852640889 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22475R_367
#print axioms SieveCert.rows22475R_370
