/-
# Round 710: the refined certificate at `L = 899/400` with `n = 300`, parts 453–456 of 534

File 117 of 135: the parts `rows22475R_453` … `rows22475R_456` of `SieveCert22475R.lean`'s certificate on
`SieveGrid22475R.grid22475R` (4 parts, 24764 tests: row 135 columns 0–43, row 135 columns 44–55, row 135 columns
56–299, row 136 columns 0–43), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22475R_453 : rowsJ2 135 136 0 44 ≤ 127489828557572 := by decide +kernel

theorem rows22475R_454 : rowsJ2 135 136 44 56 ≤ 59976444553016 := by decide +kernel

theorem rows22475R_455 : rowsJ2 135 136 56 300 ≤ 2451723779042244 := by decide +kernel

theorem rows22475R_456 : rowsJ2 136 137 0 44 ≤ 130953959519239 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22475R_453
#print axioms SieveCert.rows22475R_456
