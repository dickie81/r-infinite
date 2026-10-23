/-
# Round 710: the refined certificate at `L = 899/400` with `n = 300`, parts 280–283 of 534

File 72 of 135: the parts `rows22475R_280` … `rows22475R_283` of `SieveCert22475R.lean`'s certificate on
`SieveGrid22475R.grid22475R` (4 parts, 28514 tests: row 95 columns 61–65, row 95 columns 66–71, row 95 columns
72–78, row 95 columns 79–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22475R_280 : rowsJ2 95 96 61 66 ≤ 0 := by decide +kernel

theorem rows22475R_281 : rowsJ2 95 96 66 72 ≤ 72846807621 := by decide +kernel

theorem rows22475R_282 : rowsJ2 95 96 72 79 ≤ 12773453307821 := by decide +kernel

theorem rows22475R_283 : rowsJ2 95 96 79 300 ≤ 1454811482734281 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22475R_280
#print axioms SieveCert.rows22475R_283
