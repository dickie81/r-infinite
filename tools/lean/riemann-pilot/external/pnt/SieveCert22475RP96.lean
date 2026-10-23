/-
# Round 710: the refined certificate at `L = 899/400` with `n = 300`, parts 371–373 of 534

File 96 of 135: the parts `rows22475R_371` … `rows22475R_373` of `SieveCert22475R.lean`'s certificate on
`SieveGrid22475R.grid22475R` (3 parts, 23421 tests: row 112 columns 51–57, row 112 columns 58–65, row 112 columns
66–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
(`Elab.async false`).

The file imports `SieveGrid22475R.lean`.
-/
import SieveGrid22475R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22475R

theorem rows22475R_371 : rowsJ2 112 113 51 58 ≤ 43227654764472 := by decide +kernel

theorem rows22475R_372 : rowsJ2 112 113 58 66 ≤ 15020186995070 := by decide +kernel

theorem rows22475R_373 : rowsJ2 112 113 66 300 ≤ 671671510346491 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22475R_371
#print axioms SieveCert.rows22475R_373
