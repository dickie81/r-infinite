/-
# Round 710: the refined certificate at `L = 899/400` with `n = 300`, parts 315–317 of 534

File 81 of 135: the parts `rows22475R_315` … `rows22475R_317` of `SieveCert22475R.lean`'s certificate on
`SieveGrid22475R.grid22475R` (3 parts, 22811 tests: row 101 columns 53–59, row 101 columns 60–65, row 101 columns
66–72), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows22475R_315 : rowsJ2 101 102 53 60 ≤ 3825669322454 := by decide +kernel

theorem rows22475R_316 : rowsJ2 101 102 60 66 ≤ 0 := by decide +kernel

theorem rows22475R_317 : rowsJ2 101 102 66 73 ≤ 1143571921928 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22475R_315
#print axioms SieveCert.rows22475R_317
