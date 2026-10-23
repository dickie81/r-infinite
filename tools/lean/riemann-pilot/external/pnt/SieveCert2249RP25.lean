/-
# Round 710: the refined certificate at `L = 2249/1000` with `n = 300`, parts 98–100 of 503

File 25 of 127: the parts `rows2249R_98` … `rows2249R_100` of `SieveCert2249R.lean`'s certificate on
`SieveGrid2249R.grid2249R` (3 parts, 22916 tests: row 63 columns 0–34, row 63 columns 35–44, row 63 columns 45–299),
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

theorem rows2249R_98 : rowsJ2 63 64 0 35 ≤ 745060928772724 := by decide +kernel

theorem rows2249R_99 : rowsJ2 63 64 35 45 ≤ 536956018625384 := by decide +kernel

theorem rows2249R_100 : rowsJ2 63 64 45 300 ≤ 763478092908593 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2249R_98
#print axioms SieveCert.rows2249R_100
