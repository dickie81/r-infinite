/-
# Round 710: the refined certificate at `L = 899/400` with `n = 300`, parts 296–299 of 534

File 76 of 135: the parts `rows22475R_296` … `rows22475R_299` of `SieveCert22475R.lean`'s certificate on
`SieveGrid22475R.grid22475R` (4 parts, 29525 tests: row 98 columns 0–52, row 98 columns 53–60, row 98 columns 61–65,
row 98 columns 66–71), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one
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

theorem rows22475R_296 : rowsJ2 98 99 0 53 ≤ 585662954006605 := by decide +kernel

theorem rows22475R_297 : rowsJ2 98 99 53 61 ≤ 283440073709 := by decide +kernel

theorem rows22475R_298 : rowsJ2 98 99 61 66 ≤ 0 := by decide +kernel

theorem rows22475R_299 : rowsJ2 98 99 66 72 ≤ 229690552246 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22475R_296
#print axioms SieveCert.rows22475R_299
