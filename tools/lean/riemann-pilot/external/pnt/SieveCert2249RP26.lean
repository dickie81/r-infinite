/-
# Round 710: the refined certificate at `L = 2249/1000` with `n = 300`, parts 101–103 of 503

File 26 of 127: the parts `rows2249R_101` … `rows2249R_103` of `SieveCert2249R.lean`'s certificate on
`SieveGrid2249R.grid2249R` (3 parts, 22661 tests: row 64 columns 0–34, row 64 columns 35–44, row 64 columns 45–299),
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

theorem rows2249R_101 : rowsJ2 64 65 0 35 ≤ 705820593567621 := by decide +kernel

theorem rows2249R_102 : rowsJ2 64 65 35 45 ≤ 542342846922367 := by decide +kernel

theorem rows2249R_103 : rowsJ2 64 65 45 300 ≤ 748691428043044 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2249R_101
#print axioms SieveCert.rows2249R_103
