/-
# Round 710: the refined certificate at `L = 899/400` with `n = 300`, parts 384–387 of 534

File 100 of 135: the parts `rows22475R_384` … `rows22475R_387` of `SieveCert22475R.lean`'s certificate on
`SieveGrid22475R.grid22475R` (4 parts, 29410 tests: row 115 columns 57–64, row 115 columns 65–299, row 116 columns
0–49, row 116 columns 50–56), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22475R_384 : rowsJ2 115 116 57 65 ≤ 18576794674513 := by decide +kernel

theorem rows22475R_385 : rowsJ2 115 116 65 300 ≤ 447973320413749 := by decide +kernel

theorem rows22475R_386 : rowsJ2 116 117 0 50 ≤ 265085484155846 := by decide +kernel

theorem rows22475R_387 : rowsJ2 116 117 50 57 ≤ 52566468043651 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22475R_384
#print axioms SieveCert.rows22475R_387
