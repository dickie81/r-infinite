/-
# Round 710: the refined certificate at `L = 899/400` with `n = 300`, parts 457–460 of 534

File 118 of 135: the parts `rows22475R_457` … `rows22475R_460` of `SieveCert22475R.lean`'s certificate on
`SieveGrid22475R.grid22475R` (4 parts, 24638 tests: row 136 columns 44–56, row 136 columns 57–299, row 137 columns
0–43, row 137 columns 44–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22475R_457 : rowsJ2 136 137 44 57 ≤ 54992945747782 := by decide +kernel

theorem rows22475R_458 : rowsJ2 136 137 57 300 ≤ 2451997178154917 := by decide +kernel

theorem rows22475R_459 : rowsJ2 137 138 0 44 ≤ 133506966848262 := by decide +kernel

theorem rows22475R_460 : rowsJ2 137 138 44 300 ≤ 2503505577074518 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22475R_457
#print axioms SieveCert.rows22475R_460
