/-
# Round 710: the refined certificate at `L = 2249/1000` with `n = 300`, parts 158–160 of 503

File 42 of 127: the parts `rows2249R_158` … `rows2249R_160` of `SieveCert2249R.lean`'s certificate on
`SieveGrid2249R.grid2249R` (3 parts, 23643 tests: row 78 columns 35–61, row 78 columns 62–68, row 78 columns 69–73),
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

theorem rows2249R_158 : rowsJ2 78 79 35 62 ≤ 671875712788878 := by decide +kernel

theorem rows2249R_159 : rowsJ2 78 79 62 69 ≤ 9826147809206 := by decide +kernel

theorem rows2249R_160 : rowsJ2 78 79 69 74 ≤ 11431106893773 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2249R_158
#print axioms SieveCert.rows2249R_160
