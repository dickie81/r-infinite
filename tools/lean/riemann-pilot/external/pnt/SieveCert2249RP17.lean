/-
# Round 710: the refined certificate at `L = 2249/1000` with `n = 300`, parts 67–70 of 503

File 17 of 127: the parts `rows2249R_67` … `rows2249R_70` of `SieveCert2249R.lean`'s certificate on
`SieveGrid2249R.grid2249R` (4 parts, 24850 tests: row 55 columns 0–34, row 55 columns 35–43, row 55 columns 44–52,
row 55 columns 53–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`,
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

theorem rows2249R_67 : rowsJ2 55 56 0 35 ≤ 1163027257451476 := by decide +kernel

theorem rows2249R_68 : rowsJ2 55 56 35 44 ≤ 369689726671858 := by decide +kernel

theorem rows2249R_69 : rowsJ2 55 56 44 53 ≤ 587011563333991 := by decide +kernel

theorem rows2249R_70 : rowsJ2 55 56 53 300 ≤ 164740590711878 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2249R_67
#print axioms SieveCert.rows2249R_70
