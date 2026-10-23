/-
# Round 710: the refined certificate at `L = 2249/1000` with `n = 300`, parts 177–180 of 503

File 47 of 127: the parts `rows2249R_177` … `rows2249R_180` of `SieveCert2249R.lean`'s certificate on
`SieveGrid2249R.grid2249R` (4 parts, 27678 tests: row 81 columns 68–72, row 81 columns 73–77, row 81 columns 78–299,
row 82 columns 0–36), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one
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

theorem rows2249R_177 : rowsJ2 81 82 68 73 ≤ 6610275086570 := by decide +kernel

theorem rows2249R_178 : rowsJ2 81 82 73 78 ≤ 3162702442864 := by decide +kernel

theorem rows2249R_179 : rowsJ2 81 82 78 300 ≤ 4044737858231 := by decide +kernel

theorem rows2249R_180 : rowsJ2 82 83 0 37 ≤ 562496611069590 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2249R_177
#print axioms SieveCert.rows2249R_180
