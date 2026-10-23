/-
# Round 710: the refined certificate at `L = 2249/1000` with `n = 300`, parts 342–344 of 503

File 90 of 127: the parts `rows2249R_342` … `rows2249R_344` of `SieveCert2249R.lean`'s certificate on
`SieveGrid2249R.grid2249R` (3 parts, 22883 tests: row 110 columns 51–57, row 110 columns 58–65, row 110 columns
66–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
(`Elab.async false`).

The file imports `SieveGrid2249R.lean`.
-/
import SieveGrid2249R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid2249R

theorem rows2249R_342 : rowsJ2 110 111 51 58 ≤ 34242791774908 := by decide +kernel

theorem rows2249R_343 : rowsJ2 110 111 58 66 ≤ 8290151082932 := by decide +kernel

theorem rows2249R_344 : rowsJ2 110 111 66 300 ≤ 561759763103412 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2249R_342
#print axioms SieveCert.rows2249R_344
