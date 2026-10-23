/-
# Round 710: the refined certificate at `L = 2249/1000` with `n = 300`, parts 220–223 of 503

File 58 of 127: the parts `rows2249R_220` … `rows2249R_223` of `SieveCert2249R.lean`'s certificate on
`SieveGrid2249R.grid2249R` (4 parts, 28087 tests: row 88 columns 62–66, row 88 columns 67–71, row 88 columns 72–77,
row 88 columns 78–84), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one
at a time (`Elab.async false`).

The file imports `SieveGrid2249R.lean`.
-/
import SieveGrid2249R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid2249R

theorem rows2249R_220 : rowsJ2 88 89 62 67 ≤ 491194430271 := by decide +kernel

theorem rows2249R_221 : rowsJ2 88 89 67 72 ≤ 159277102472 := by decide +kernel

theorem rows2249R_222 : rowsJ2 88 89 72 78 ≤ 2621030444203 := by decide +kernel

theorem rows2249R_223 : rowsJ2 88 89 78 85 ≤ 32568003551589 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2249R_220
#print axioms SieveCert.rows2249R_223
