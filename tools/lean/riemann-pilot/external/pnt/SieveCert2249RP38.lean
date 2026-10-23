/-
# Round 710: the refined certificate at `L = 2249/1000` with `n = 300`, parts 143–146 of 503

File 38 of 127: the parts `rows2249R_143` … `rows2249R_146` of `SieveCert2249R.lean`'s certificate on
`SieveGrid2249R.grid2249R` (4 parts, 26628 tests: row 75 columns 35–60, row 75 columns 61–68, row 75 columns 69–73,
row 75 columns 74–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`,
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

theorem rows2249R_143 : rowsJ2 75 76 35 61 ≤ 803241208738946 := by decide +kernel

theorem rows2249R_144 : rowsJ2 75 76 61 69 ≤ 32758843773986 := by decide +kernel

theorem rows2249R_145 : rowsJ2 75 76 69 74 ≤ 16906752940755 := by decide +kernel

theorem rows2249R_146 : rowsJ2 75 76 74 300 ≤ 6253267584199 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2249R_143
#print axioms SieveCert.rows2249R_146
