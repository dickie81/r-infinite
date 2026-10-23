/-
# Round 710: the refined certificate at `L = 899/400` with `n = 300`, parts 412–415 of 534

File 107 of 135: the parts `rows22475R_412` … `rows22475R_415` of `SieveCert22475R.lean`'s certificate on
`SieveGrid22475R.grid22475R` (4 parts, 25048 tests: row 122 columns 56–66, row 122 columns 67–299, row 123 columns
0–47, row 123 columns 48–55), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22475R_412 : rowsJ2 122 123 56 67 ≤ 11055055982717 := by decide +kernel

theorem rows22475R_413 : rowsJ2 122 123 67 300 ≤ 795111175594520 := by decide +kernel

theorem rows22475R_414 : rowsJ2 123 124 0 48 ≤ 189552888049128 := by decide +kernel

theorem rows22475R_415 : rowsJ2 123 124 48 56 ≤ 60696919887899 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22475R_412
#print axioms SieveCert.rows22475R_415
