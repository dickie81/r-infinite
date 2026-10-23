/-
# Round 710: the refined certificate at `L = 2249/1000` with `n = 300`, parts 113–116 of 503

File 30 of 127: the parts `rows2249R_113` … `rows2249R_116` of `SieveCert2249R.lean`'s certificate on
`SieveGrid2249R.grid2249R` (4 parts, 24104 tests: row 68 columns 0–34, row 68 columns 35–47, row 68 columns 48–67,
row 68 columns 68–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`,
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

theorem rows2249R_113 : rowsJ2 68 69 0 35 ≤ 583309480156196 := by decide +kernel

theorem rows2249R_114 : rowsJ2 68 69 35 48 ≤ 685345837708705 := by decide +kernel

theorem rows2249R_115 : rowsJ2 68 69 48 68 ≤ 498462192236593 := by decide +kernel

theorem rows2249R_116 : rowsJ2 68 69 68 300 ≤ 9482840468946 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2249R_113
#print axioms SieveCert.rows2249R_116
