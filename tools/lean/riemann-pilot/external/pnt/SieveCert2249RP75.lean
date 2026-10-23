/-
# Round 710: the refined certificate at `L = 2249/1000` with `n = 300`, parts 285–288 of 503

File 75 of 127: the parts `rows2249R_285` … `rows2249R_288` of `SieveCert2249R.lean`'s certificate on
`SieveGrid2249R.grid2249R` (4 parts, 29377 tests: row 99 columns 0–52, row 99 columns 53–59, row 99 columns 60–65,
row 99 columns 66–72), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one
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

theorem rows2249R_285 : rowsJ2 99 100 0 53 ≤ 470689195753334 := by decide +kernel

theorem rows2249R_286 : rowsJ2 99 100 53 60 ≤ 365736252029 := by decide +kernel

theorem rows2249R_287 : rowsJ2 99 100 60 66 ≤ 0 := by decide +kernel

theorem rows2249R_288 : rowsJ2 99 100 66 73 ≤ 1035380171142 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2249R_285
#print axioms SieveCert.rows2249R_288
