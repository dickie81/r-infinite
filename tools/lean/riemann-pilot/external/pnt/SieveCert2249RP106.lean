/-
# Round 710: the refined certificate at `L = 2249/1000` with `n = 300`, parts 404–407 of 503

File 106 of 127: the parts `rows2249R_404` … `rows2249R_407` of `SieveCert2249R.lean`'s certificate on
`SieveGrid2249R.grid2249R` (4 parts, 27502 tests: row 127 columns 0–45, row 127 columns 46–55, row 127 columns
56–299, row 128 columns 0–45), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
+kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid2249R.lean`.
-/
import SieveGrid2249R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid2249R

theorem rows2249R_404 : rowsJ2 127 128 0 46 ≤ 133076771735221 := by decide +kernel

theorem rows2249R_405 : rowsJ2 127 128 46 56 ≤ 50807465629656 := by decide +kernel

theorem rows2249R_406 : rowsJ2 127 128 56 300 ≤ 1526889891390997 := by decide +kernel

theorem rows2249R_407 : rowsJ2 128 129 0 46 ≤ 131132529197432 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2249R_404
#print axioms SieveCert.rows2249R_407
