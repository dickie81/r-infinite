/-
# Round 710: the refined certificate at `L = 899/400` with `n = 300`, parts 522–525 of 534

File 133 of 135: the parts `rows22475R_522` … `rows22475R_525` of `SieveCert22475R.lean`'s certificate on
`SieveGrid22475R.grid22475R` (4 parts, 27134 tests: rows 213–215, rows 216–218, rows 219–221, rows 222–224), each a
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

theorem rows22475R_522 : rows2 213 216 ≤ 30522659979475376 := by decide +kernel

theorem rows22475R_523 : rows2 216 219 ≤ 30883712440013432 := by decide +kernel

theorem rows22475R_524 : rows2 219 222 ≤ 31030103178573779 := by decide +kernel

theorem rows22475R_525 : rows2 222 225 ≤ 31398683081346703 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22475R_522
#print axioms SieveCert.rows22475R_525
