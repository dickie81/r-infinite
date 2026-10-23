/-
# Round 710: the refined certificate at `L = 2249/1000` with `n = 300`, parts 274–276 of 503

File 72 of 127: the parts `rows2249R_274` … `rows2249R_276` of `SieveCert2249R.lean`'s certificate on
`SieveGrid2249R.grid2249R` (3 parts, 22647 tests: row 97 columns 54–60, row 97 columns 61–66, row 97 columns 67–73),
each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
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

theorem rows2249R_274 : rowsJ2 97 98 54 61 ≤ 0 := by decide +kernel

theorem rows2249R_275 : rowsJ2 97 98 61 67 ≤ 0 := by decide +kernel

theorem rows2249R_276 : rowsJ2 97 98 67 74 ≤ 1774739899280 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2249R_274
#print axioms SieveCert.rows2249R_276
