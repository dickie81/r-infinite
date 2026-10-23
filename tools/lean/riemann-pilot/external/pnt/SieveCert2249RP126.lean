/-
# Round 710: the refined certificate at `L = 2249/1000` with `n = 300`, parts 494–497 of 503

File 126 of 127: the parts `rows2249R_494` … `rows2249R_497` of `SieveCert2249R.lean`'s certificate on
`SieveGrid2249R.grid2249R` (4 parts, 28875 tests: rows 222–224, rows 225–228, rows 229–232, rows 233–236), each a
sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
false`).

The file imports `SieveGrid2249R.lean`.
-/
import SieveGrid2249R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid2249R

theorem rows2249R_494 : rows2 222 225 ≤ 30523271612753853 := by decide +kernel

theorem rows2249R_495 : rows2 225 229 ≤ 41118379641699892 := by decide +kernel

theorem rows2249R_496 : rows2 229 233 ≤ 41469379569153664 := by decide +kernel

theorem rows2249R_497 : rows2 233 237 ≤ 41778390601826207 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2249R_494
#print axioms SieveCert.rows2249R_497
