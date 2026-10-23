/-
# Round 710: the refined certificate at `L = 899/400` with `n = 300`, parts 400–403 of 534

File 104 of 135: the parts `rows22475R_400` … `rows22475R_403` of `SieveCert22475R.lean`'s certificate on
`SieveGrid22475R.grid22475R` (4 parts, 26947 tests: row 119 columns 56–64, row 119 columns 65–299, row 120 columns
0–48, row 120 columns 49–55), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22475R_400 : rowsJ2 119 120 56 65 ≤ 16880582367515 := by decide +kernel

theorem rows22475R_401 : rowsJ2 119 120 65 300 ≤ 324912355260737 := by decide +kernel

theorem rows22475R_402 : rowsJ2 120 121 0 49 ≤ 219803415148317 := by decide +kernel

theorem rows22475R_403 : rowsJ2 120 121 49 56 ≤ 56460477706499 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22475R_400
#print axioms SieveCert.rows22475R_403
