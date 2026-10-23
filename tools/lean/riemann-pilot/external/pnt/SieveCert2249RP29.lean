/-
# Round 710: the refined certificate at `L = 2249/1000` with `n = 300`, parts 110–112 of 503

File 29 of 127: the parts `rows2249R_110` … `rows2249R_112` of `SieveCert2249R.lean`'s certificate on
`SieveGrid2249R.grid2249R` (3 parts, 23413 tests: row 67 columns 0–34, row 67 columns 35–46, row 67 columns 47–299),
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

theorem rows2249R_110 : rowsJ2 67 68 0 35 ≤ 608677761796682 := by decide +kernel

theorem rows2249R_111 : rowsJ2 67 68 35 47 ≤ 648008266791448 := by decide +kernel

theorem rows2249R_112 : rowsJ2 67 68 47 300 ≤ 579633134827972 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2249R_110
#print axioms SieveCert.rows2249R_112
