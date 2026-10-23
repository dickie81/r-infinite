/-
# Round 710: the refined certificate at `L = 2249/1000` with `n = 300`, parts 20–23 of 503

File 5 of 127: the parts `rows2249R_20` … `rows2249R_23` of `SieveCert2249R.lean`'s certificate on
`SieveGrid2249R.grid2249R` (4 parts, 23821 tests: row 39 columns 0–34, row 39 columns 35–299, row 40 columns 0–34,
row 40 columns 35–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`,
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

theorem rows2249R_20 : rowsJ2 39 40 0 35 ≤ 2306124148250552 := by decide +kernel

theorem rows2249R_21 : rowsJ2 39 40 35 300 ≤ 279878107629007 := by decide +kernel

theorem rows2249R_22 : rowsJ2 40 41 0 35 ≤ 2229630673599475 := by decide +kernel

theorem rows2249R_23 : rowsJ2 40 41 35 300 ≤ 310261176317248 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2249R_20
#print axioms SieveCert.rows2249R_23
