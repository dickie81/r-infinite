/-
# Round 710: the refined certificate at `L = 2249/1000` with `n = 300`, parts 478–481 of 503

File 122 of 127: the parts `rows2249R_478` … `rows2249R_481` of `SieveCert2249R.lean`'s certificate on
`SieveGrid2249R.grid2249R` (4 parts, 27221 tests: rows 169–170, rows 171–173, rows 174–176, rows 177–180), each a
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

theorem rows2249R_478 : rows2 169 171 ≤ 9416686573912414 := by decide +kernel

theorem rows2249R_479 : rows2 171 174 ≤ 15128700154599422 := by decide +kernel

theorem rows2249R_480 : rows2 174 177 ≤ 16382693736880571 := by decide +kernel

theorem rows2249R_481 : rows2 177 181 ≤ 23878677910863062 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2249R_478
#print axioms SieveCert.rows2249R_481
