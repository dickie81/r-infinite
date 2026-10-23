/-
# Round 710: the refined certificate at `L = 2249/1000` with `n = 300`, parts 91–94 of 503

File 23 of 127: the parts `rows2249R_91` … `rows2249R_94` of `SieveCert2249R.lean`'s certificate on
`SieveGrid2249R.grid2249R` (4 parts, 23814 tests: row 61 columns 0–34, row 61 columns 35–44, row 61 columns 45–60,
row 61 columns 61–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`,
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

theorem rows2249R_91 : rowsJ2 61 62 0 35 ≤ 833354061381145 := by decide +kernel

theorem rows2249R_92 : rowsJ2 61 62 35 45 ≤ 518742931481094 := by decide +kernel

theorem rows2249R_93 : rowsJ2 61 62 45 61 ≤ 746783579935029 := by decide +kernel

theorem rows2249R_94 : rowsJ2 61 62 61 300 ≤ 30590064228280 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2249R_91
#print axioms SieveCert.rows2249R_94
