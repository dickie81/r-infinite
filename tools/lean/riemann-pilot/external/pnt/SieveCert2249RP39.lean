/-
# Round 710: the refined certificate at `L = 2249/1000` with `n = 300`, parts 147–149 of 503

File 39 of 127: the parts `rows2249R_147` … `rows2249R_149` of `SieveCert2249R.lean`'s certificate on
`SieveGrid2249R.grid2249R` (3 parts, 23250 tests: row 76 columns 0–34, row 76 columns 35–60, row 76 columns 61–68),
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

theorem rows2249R_147 : rowsJ2 76 77 0 35 ≤ 492196871070973 := by decide +kernel

theorem rows2249R_148 : rowsJ2 76 77 35 61 ≤ 757746696572487 := by decide +kernel

theorem rows2249R_149 : rowsJ2 76 77 61 69 ≤ 25084689164207 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2249R_147
#print axioms SieveCert.rows2249R_149
