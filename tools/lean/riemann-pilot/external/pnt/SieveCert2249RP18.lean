/-
# Round 710: the refined certificate at `L = 2249/1000` with `n = 300`, parts 71–74 of 503

File 18 of 127: the parts `rows2249R_71` … `rows2249R_74` of `SieveCert2249R.lean`'s certificate on
`SieveGrid2249R.grid2249R` (4 parts, 24904 tests: row 56 columns 0–34, row 56 columns 35–43, row 56 columns 44–52,
row 56 columns 53–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`,
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

theorem rows2249R_71 : rowsJ2 56 57 0 35 ≤ 1102578165458804 := by decide +kernel

theorem rows2249R_72 : rowsJ2 56 57 35 44 ≤ 383833564716633 := by decide +kernel

theorem rows2249R_73 : rowsJ2 56 57 44 53 ≤ 572170602661789 := by decide +kernel

theorem rows2249R_74 : rowsJ2 56 57 53 300 ≤ 208945476327128 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2249R_71
#print axioms SieveCert.rows2249R_74
