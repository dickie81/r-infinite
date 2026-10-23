/-
# Round 710: the refined certificate at `L = 2249/1000` with `n = 300`, parts 79–82 of 503

File 20 of 127: the parts `rows2249R_79` … `rows2249R_82` of `SieveCert2249R.lean`'s certificate on
`SieveGrid2249R.grid2249R` (4 parts, 24726 tests: row 58 columns 0–34, row 58 columns 35–43, row 58 columns 44–54,
row 58 columns 55–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`,
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

theorem rows2249R_79 : rowsJ2 58 59 0 35 ≤ 987574183369147 := by decide +kernel

theorem rows2249R_80 : rowsJ2 58 59 35 44 ≤ 414134539200379 := by decide +kernel

theorem rows2249R_81 : rowsJ2 58 59 44 55 ≤ 642965002595600 := by decide +kernel

theorem rows2249R_82 : rowsJ2 58 59 55 300 ≤ 179569191988451 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2249R_79
#print axioms SieveCert.rows2249R_82
