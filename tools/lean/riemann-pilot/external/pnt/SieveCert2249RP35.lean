/-
# Round 710: the refined certificate at `L = 2249/1000` with `n = 300`, parts 133–135 of 503

File 35 of 127: the parts `rows2249R_133` … `rows2249R_135` of `SieveCert2249R.lean`'s certificate on
`SieveGrid2249R.grid2249R` (3 parts, 23341 tests: row 73 columns 0–34, row 73 columns 35–57, row 73 columns 58–68),
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

theorem rows2249R_133 : rowsJ2 73 74 0 35 ≤ 505623460850036 := by decide +kernel

theorem rows2249R_134 : rowsJ2 73 74 35 58 ≤ 854769472152875 := by decide +kernel

theorem rows2249R_135 : rowsJ2 73 74 58 69 ≤ 91374954676932 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2249R_133
#print axioms SieveCert.rows2249R_135
