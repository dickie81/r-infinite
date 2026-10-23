/-
# Round 710: the refined certificate at `L = 2249/1000` with `n = 300`, parts 75–78 of 503

File 19 of 127: the parts `rows2249R_75` … `rows2249R_78` of `SieveCert2249R.lean`'s certificate on
`SieveGrid2249R.grid2249R` (4 parts, 24875 tests: row 57 columns 0–34, row 57 columns 35–43, row 57 columns 44–53,
row 57 columns 54–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`,
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

theorem rows2249R_75 : rowsJ2 57 58 0 35 ≤ 1043897573520769 := by decide +kernel

theorem rows2249R_76 : rowsJ2 57 58 35 44 ≤ 400173722366475 := by decide +kernel

theorem rows2249R_77 : rowsJ2 57 58 44 54 ≤ 610288440802969 := by decide +kernel

theorem rows2249R_78 : rowsJ2 57 58 54 300 ≤ 194445932744429 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2249R_75
#print axioms SieveCert.rows2249R_78
