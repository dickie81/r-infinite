/-
# Round 710: the refined certificate at `L = 899/400` with `n = 300`, parts 526–529 of 534

File 134 of 135: the parts `rows22475R_526` … `rows22475R_529` of `SieveCert22475R.lean`'s certificate on
`SieveGrid22475R.grid22475R` (4 parts, 28481 tests: rows 225–227, rows 228–231, rows 232–235, rows 236–285), each a
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

theorem rows22475R_526 : rows2 225 228 ≤ 31519426251162577 := by decide +kernel

theorem rows22475R_527 : rows2 228 232 ≤ 42458401593160912 := by decide +kernel

theorem rows22475R_528 : rows2 232 236 ≤ 42826518602921504 := by decide +kernel

theorem rows22475R_529 : rows2 236 286 ≤ 43134139432887261 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22475R_526
#print axioms SieveCert.rows22475R_529
