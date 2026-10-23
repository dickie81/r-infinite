/-
# Round 710: the refined certificate at `L = 2249/1000` with `n = 300`, parts 48–50 of 503

File 12 of 127: the parts `rows2249R_48` … `rows2249R_50` of `SieveCert2249R.lean`'s certificate on
`SieveGrid2249R.grid2249R` (3 parts, 22658 tests: row 50 columns 0–34, row 50 columns 35–43, row 50 columns 44–299),
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

theorem rows2249R_48 : rowsJ2 50 51 0 35 ≤ 1492139514169183 := by decide +kernel

theorem rows2249R_49 : rowsJ2 50 51 35 44 ≤ 337074181537311 := by decide +kernel

theorem rows2249R_50 : rowsJ2 50 51 44 300 ≤ 489384341423341 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2249R_48
#print axioms SieveCert.rows2249R_50
