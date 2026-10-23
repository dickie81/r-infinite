/-
# Round 710: the refined certificate at `L = 2249/1000` with `n = 300`, parts 464–467 of 503

File 119 of 127: the parts `rows2249R_464` … `rows2249R_467` of `SieveCert2249R.lean`'s certificate on
`SieveGrid2249R.grid2249R` (4 parts, 28657 tests: rows 153–153, rows 154–154, rows 155–155, rows 156–156), each a
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

theorem rows2249R_464 : rows2 153 154 ≤ 2653711234971205 := by decide +kernel

theorem rows2249R_465 : rows2 154 155 ≤ 2674000067624222 := by decide +kernel

theorem rows2249R_466 : rows2 155 156 ≤ 2697952468973721 := by decide +kernel

theorem rows2249R_467 : rows2 156 157 ≤ 2789549758854008 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2249R_464
#print axioms SieveCert.rows2249R_467
