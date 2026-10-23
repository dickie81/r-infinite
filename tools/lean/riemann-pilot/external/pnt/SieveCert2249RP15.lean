/-
# Round 710: the refined certificate at `L = 2249/1000` with `n = 300`, parts 59–62 of 503

File 15 of 127: the parts `rows2249R_59` … `rows2249R_62` of `SieveCert2249R.lean`'s certificate on
`SieveGrid2249R.grid2249R` (4 parts, 24372 tests: row 53 columns 0–34, row 53 columns 35–43, row 53 columns 44–51,
row 53 columns 52–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`,
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

theorem rows2249R_59 : rowsJ2 53 54 0 35 ≤ 1289930862726294 := by decide +kernel

theorem rows2249R_60 : rowsJ2 53 54 35 44 ≤ 348773501887989 := by decide +kernel

theorem rows2249R_61 : rowsJ2 53 54 44 52 ≤ 546314571632625 := by decide +kernel

theorem rows2249R_62 : rowsJ2 53 54 52 300 ≤ 121916955365821 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2249R_59
#print axioms SieveCert.rows2249R_62
