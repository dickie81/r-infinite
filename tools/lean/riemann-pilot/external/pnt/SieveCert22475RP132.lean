/-
# Round 710: the refined certificate at `L = 899/400` with `n = 300`, parts 518–521 of 534

File 132 of 135: the parts `rows22475R_518` … `rows22475R_521` of `SieveCert22475R.lean`'s certificate on
`SieveGrid22475R.grid22475R` (4 parts, 27582 tests: rows 201–203, rows 204–206, rows 207–209, rows 210–212), each a
sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
false`).

The file imports `SieveGrid22475R.lean`.
-/
import SieveGrid22475R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22475R

theorem rows22475R_518 : rows2 201 204 ≤ 26399774033901236 := by decide +kernel

theorem rows22475R_519 : rows2 204 207 ≤ 27529806106814226 := by decide +kernel

theorem rows22475R_520 : rows2 207 210 ≤ 28814967417406408 := by decide +kernel

theorem rows22475R_521 : rows2 210 213 ≤ 30137607748196546 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22475R_518
#print axioms SieveCert.rows22475R_521
