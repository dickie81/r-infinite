/-
# Round 710: the refined certificate at `L = 2249/1000` with `n = 300`, parts 139–142 of 503

File 37 of 127: the parts `rows2249R_139` … `rows2249R_142` of `SieveCert2249R.lean`'s certificate on
`SieveGrid2249R.grid2249R` (4 parts, 24883 tests: row 74 columns 60–68, row 74 columns 69–73, row 74 columns 74–299,
row 75 columns 0–34), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one
at a time (`Elab.async false`).

The file imports `SieveGrid2249R.lean`.
-/
import SieveGrid2249R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid2249R

theorem rows2249R_139 : rowsJ2 74 75 60 69 ≤ 51900932904482 := by decide +kernel

theorem rows2249R_140 : rowsJ2 74 75 69 74 ≤ 18551917276637 := by decide +kernel

theorem rows2249R_141 : rowsJ2 74 75 74 300 ≤ 3849463242072 := by decide +kernel

theorem rows2249R_142 : rowsJ2 75 76 0 35 ≤ 496720051353845 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2249R_139
#print axioms SieveCert.rows2249R_142
