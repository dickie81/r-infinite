/-
# Round 710: the refined certificate at `L = 2249/1000` with `n = 300`, parts 55–58 of 503

File 14 of 127: the parts `rows2249R_55` … `rows2249R_58` of `SieveCert2249R.lean`'s certificate on
`SieveGrid2249R.grid2249R` (4 parts, 23932 tests: row 52 columns 0–34, row 52 columns 35–43, row 52 columns 44–51,
row 52 columns 52–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`,
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

theorem rows2249R_55 : rowsJ2 52 53 0 35 ≤ 1355905315906975 := by decide +kernel

theorem rows2249R_56 : rowsJ2 52 53 35 44 ≤ 342121075715489 := by decide +kernel

theorem rows2249R_57 : rowsJ2 52 53 44 52 ≤ 551162980810774 := by decide +kernel

theorem rows2249R_58 : rowsJ2 52 53 52 300 ≤ 63526366725545 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2249R_55
#print axioms SieveCert.rows2249R_58
