/-
# Round 710: the refined certificate at `L = 2249/1000` with `n = 300`, parts 129–132 of 503

File 34 of 127: the parts `rows2249R_129` … `rows2249R_132` of `SieveCert2249R.lean`'s certificate on
`SieveGrid2249R.grid2249R` (4 parts, 29367 tests: row 72 columns 0–34, row 72 columns 35–53, row 72 columns 54–68,
row 72 columns 69–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`,
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

theorem rows2249R_129 : rowsJ2 72 73 0 35 ≤ 514812550747495 := by decide +kernel

theorem rows2249R_130 : rowsJ2 72 73 35 54 ≤ 808411062395849 := by decide +kernel

theorem rows2249R_131 : rowsJ2 72 73 54 69 ≤ 189792943589837 := by decide +kernel

theorem rows2249R_132 : rowsJ2 72 73 69 300 ≤ 18034204722885 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2249R_129
#print axioms SieveCert.rows2249R_132
