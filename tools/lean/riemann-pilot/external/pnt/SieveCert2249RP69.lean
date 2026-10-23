/-
# Round 710: the refined certificate at `L = 2249/1000` with `n = 300`, parts 263–266 of 503

File 69 of 127: the parts `rows2249R_263` … `rows2249R_266` of `SieveCert2249R.lean`'s certificate on
`SieveGrid2249R.grid2249R` (4 parts, 25435 tests: row 95 columns 61–66, row 95 columns 67–73, row 95 columns 74–81,
row 95 columns 82–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`,
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

theorem rows2249R_263 : rowsJ2 95 96 61 67 ≤ 0 := by decide +kernel

theorem rows2249R_264 : rowsJ2 95 96 67 74 ≤ 1264605572371 := by decide +kernel

theorem rows2249R_265 : rowsJ2 95 96 74 82 ≤ 33681517385074 := by decide +kernel

theorem rows2249R_266 : rowsJ2 95 96 82 300 ≤ 1504471310253752 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2249R_263
#print axioms SieveCert.rows2249R_266
