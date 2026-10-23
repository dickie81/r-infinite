/-
# Round 710: the refined certificate at `L = 2249/1000` with `n = 300`, parts 117–120 of 503

File 31 of 127: the parts `rows2249R_117` … `rows2249R_120` of `SieveCert2249R.lean`'s certificate on
`SieveGrid2249R.grid2249R` (4 parts, 25084 tests: row 69 columns 0–34, row 69 columns 35–48, row 69 columns 49–67,
row 69 columns 68–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`,
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

theorem rows2249R_117 : rowsJ2 69 70 0 35 ≤ 561060787455263 := by decide +kernel

theorem rows2249R_118 : rowsJ2 69 70 35 49 ≤ 716579517465766 := by decide +kernel

theorem rows2249R_119 : rowsJ2 69 70 49 68 ≤ 423648606832898 := by decide +kernel

theorem rows2249R_120 : rowsJ2 69 70 68 300 ≤ 15697687633341 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2249R_117
#print axioms SieveCert.rows2249R_120
