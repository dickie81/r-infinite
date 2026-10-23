/-
# Round 710: the refined certificate at `L = 899/400` with `n = 300`, parts 272–275 of 534

File 70 of 135: the parts `rows22475R_272` … `rows22475R_275` of `SieveCert22475R.lean`'s certificate on
`SieveGrid22475R.grid22475R` (4 parts, 29610 tests: row 94 columns 0–52, row 94 columns 53–60, row 94 columns 61–65,
row 94 columns 66–71), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one
at a time (`Elab.async false`).

The file imports `SieveGrid22475R.lean`.
-/
import SieveGrid22475R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22475R

theorem rows22475R_272 : rowsJ2 94 95 0 53 ≤ 692102481188657 := by decide +kernel

theorem rows22475R_273 : rowsJ2 94 95 53 61 ≤ 0 := by decide +kernel

theorem rows22475R_274 : rowsJ2 94 95 61 66 ≤ 0 := by decide +kernel

theorem rows22475R_275 : rowsJ2 94 95 66 72 ≤ 71359974796 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22475R_272
#print axioms SieveCert.rows22475R_275
