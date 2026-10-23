/-
# Round 710: the refined certificate at `L = 2249/1000` with `n = 300`, parts 154–157 of 503

File 41 of 127: the parts `rows2249R_154` … `rows2249R_157` of `SieveCert2249R.lean`'s certificate on
`SieveGrid2249R.grid2249R` (4 parts, 29849 tests: row 77 columns 61–67, row 77 columns 68–72, row 77 columns 73–299,
row 78 columns 0–34), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one
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

theorem rows2249R_154 : rowsJ2 77 78 61 68 ≤ 17080042959391 := by decide +kernel

theorem rows2249R_155 : rowsJ2 77 78 68 73 ≤ 12718012815356 := by decide +kernel

theorem rows2249R_156 : rowsJ2 77 78 73 300 ≤ 10046245943782 := by decide +kernel

theorem rows2249R_157 : rowsJ2 78 79 0 35 ≤ 486989986638856 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2249R_154
#print axioms SieveCert.rows2249R_157
