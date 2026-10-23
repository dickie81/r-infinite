/-
# Round 710: the refined certificate at `L = 2249/1000` with `n = 300`, parts 165–168 of 503

File 44 of 127: the parts `rows2249R_165` … `rows2249R_168` of `SieveCert2249R.lean`'s certificate on
`SieveGrid2249R.grid2249R` (4 parts, 25689 tests: row 79 columns 68–72, row 79 columns 73–77, row 79 columns 78–299,
row 80 columns 0–35), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one
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

theorem rows2249R_165 : rowsJ2 79 80 68 73 ≤ 9766123394650 := by decide +kernel

theorem rows2249R_166 : rowsJ2 79 80 73 78 ≤ 6069350819494 := by decide +kernel

theorem rows2249R_167 : rowsJ2 79 80 78 300 ≤ 1683333910465 := by decide +kernel

theorem rows2249R_168 : rowsJ2 80 81 0 36 ≤ 529303622172723 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2249R_165
#print axioms SieveCert.rows2249R_168
