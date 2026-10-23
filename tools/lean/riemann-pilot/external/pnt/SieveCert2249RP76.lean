/-
# Round 710: the refined certificate at `L = 2249/1000` with `n = 300`, parts 289–292 of 503

File 76 of 127: the parts `rows2249R_289` … `rows2249R_292` of `SieveCert2249R.lean`'s certificate on
`SieveGrid2249R.grid2249R` (4 parts, 22983 tests: row 99 columns 73–90, row 99 columns 91–299, row 100 columns 0–52,
row 100 columns 53–59), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`,
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

theorem rows2249R_289 : rowsJ2 99 100 73 91 ≤ 1096905773176891 := by decide +kernel

theorem rows2249R_290 : rowsJ2 99 100 91 300 ≤ 217962194334259 := by decide +kernel

theorem rows2249R_291 : rowsJ2 100 101 0 53 ≤ 450199758397966 := by decide +kernel

theorem rows2249R_292 : rowsJ2 100 101 53 60 ≤ 1146464411008 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2249R_289
#print axioms SieveCert.rows2249R_292
