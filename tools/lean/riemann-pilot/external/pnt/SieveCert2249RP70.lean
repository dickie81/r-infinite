/-
# Round 710: the refined certificate at `L = 2249/1000` with `n = 300`, parts 267–269 of 503

File 70 of 127: the parts `rows2249R_267` … `rows2249R_269` of `SieveCert2249R.lean`'s certificate on
`SieveGrid2249R.grid2249R` (3 parts, 22918 tests: row 96 columns 0–53, row 96 columns 54–60, row 96 columns 61–66),
each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
false`).

The file imports `SieveGrid2249R.lean`.
-/
import SieveGrid2249R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid2249R

theorem rows2249R_267 : rowsJ2 96 97 0 54 ≤ 532316311898412 := by decide +kernel

theorem rows2249R_268 : rowsJ2 96 97 54 61 ≤ 0 := by decide +kernel

theorem rows2249R_269 : rowsJ2 96 97 61 67 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2249R_267
#print axioms SieveCert.rows2249R_269
