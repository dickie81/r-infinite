/-
# Round 710: the refined certificate at `L = 899/400` with `n = 300`, parts 530–533 of 534

File 135 of 135: the parts `rows22475R_530` … `rows22475R_533` of `SieveCert22475R.lean`'s certificate on
`SieveGrid22475R.grid22475R` (4 parts, 24762 tests: rows 286–289, rows 290–293, rows 294–296, rows 297–299), each a
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

theorem rows22475R_530 : rows2 286 290 ≤ 50301416987465049 := by decide +kernel

theorem rows22475R_531 : rows2 290 294 ≤ 53975415560286461 := by decide +kernel

theorem rows22475R_532 : rows2 294 297 ≤ 43156069236874080 := by decide +kernel

theorem rows22475R_533 : rows2 297 300 ≤ 45767637463744005 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22475R_530
#print axioms SieveCert.rows22475R_533
