/-
# Round 710: the refined certificate at `L = 2249/1000` with `n = 300`, parts 51–54 of 503

File 13 of 127: the parts `rows2249R_51` … `rows2249R_54` of `SieveCert2249R.lean`'s certificate on
`SieveGrid2249R.grid2249R` (4 parts, 23379 tests: row 51 columns 0–34, row 51 columns 35–43, row 51 columns 44–50,
row 51 columns 51–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`,
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

theorem rows2249R_51 : rowsJ2 51 52 0 35 ≤ 1423276514393007 := by decide +kernel

theorem rows2249R_52 : rowsJ2 51 52 35 44 ≤ 338424099897073 := by decide +kernel

theorem rows2249R_53 : rowsJ2 51 52 44 51 ≤ 489299568491213 := by decide +kernel

theorem rows2249R_54 : rowsJ2 51 52 51 300 ≤ 66861473171210 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2249R_51
#print axioms SieveCert.rows2249R_54
