/-
# Round 710: the refined certificate at `L = 2249/1000` with `n = 300`, parts 281–284 of 503

File 74 of 127: the parts `rows2249R_281` … `rows2249R_284` of `SieveCert2249R.lean`'s certificate on
`SieveGrid2249R.grid2249R` (4 parts, 22767 tests: row 98 columns 61–66, row 98 columns 67–73, row 98 columns 74–91,
row 98 columns 92–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`,
one at a time (`Elab.async false`).

The file imports `SieveGrid2249R.lean`.
-/
import SieveGrid2249R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid2249R

theorem rows2249R_281 : rowsJ2 98 99 61 67 ≤ 0 := by decide +kernel

theorem rows2249R_282 : rowsJ2 98 99 67 74 ≤ 1968864999220 := by decide +kernel

theorem rows2249R_283 : rowsJ2 98 99 74 92 ≤ 1109375686053162 := by decide +kernel

theorem rows2249R_284 : rowsJ2 98 99 92 300 ≤ 219487291878561 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2249R_281
#print axioms SieveCert.rows2249R_284
