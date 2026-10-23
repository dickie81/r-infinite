/-
# Round 710: the refined certificate at `L = 899/400` with `n = 300`, parts 292–295 of 534

File 75 of 135: the parts `rows22475R_292` … `rows22475R_295` of `SieveCert22475R.lean`'s certificate on
`SieveGrid22475R.grid22475R` (4 parts, 26686 tests: row 97 columns 61–65, row 97 columns 66–71, row 97 columns
72–78, row 97 columns 79–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22475R_292 : rowsJ2 97 98 61 66 ≤ 0 := by decide +kernel

theorem rows22475R_293 : rowsJ2 97 98 66 72 ≤ 150924905217 := by decide +kernel

theorem rows22475R_294 : rowsJ2 97 98 72 79 ≤ 16010868276567 := by decide +kernel

theorem rows22475R_295 : rowsJ2 97 98 79 300 ≤ 1600338431509436 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22475R_292
#print axioms SieveCert.rows22475R_295
