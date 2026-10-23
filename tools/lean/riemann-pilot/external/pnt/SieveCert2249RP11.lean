/-
# Round 710: the refined certificate at `L = 2249/1000` with `n = 300`, parts 44–47 of 503

File 11 of 127: the parts `rows2249R_44` … `rows2249R_47` of `SieveCert2249R.lean`'s certificate on
`SieveGrid2249R.grid2249R` (4 parts, 27405 tests: row 48 columns 44–299, row 49 columns 0–34, row 49 columns 35–43,
row 49 columns 44–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`,
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

theorem rows2249R_44 : rowsJ2 48 49 44 300 ≤ 339693774326178 := by decide +kernel

theorem rows2249R_45 : rowsJ2 49 50 0 35 ≤ 1561968564664754 := by decide +kernel

theorem rows2249R_46 : rowsJ2 49 50 35 44 ≤ 338559546503111 := by decide +kernel

theorem rows2249R_47 : rowsJ2 49 50 44 300 ≤ 418334248330140 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2249R_44
#print axioms SieveCert.rows2249R_47
