/-
# Round 710: the refined certificate at `L = 2249/1000` with `n = 300`, parts 270–273 of 503

File 71 of 127: the parts `rows2249R_270` … `rows2249R_273` of `SieveCert2249R.lean`'s certificate on
`SieveGrid2249R.grid2249R` (4 parts, 24987 tests: row 96 columns 67–73, row 96 columns 74–82, row 96 columns 83–299,
row 97 columns 0–53), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one
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

theorem rows2249R_270 : rowsJ2 96 97 67 74 ≤ 1441816554575 := by decide +kernel

theorem rows2249R_271 : rowsJ2 96 97 74 83 ≤ 47011203272974 := by decide +kernel

theorem rows2249R_272 : rowsJ2 96 97 83 300 ≤ 1426723780341806 := by decide +kernel

theorem rows2249R_273 : rowsJ2 97 98 0 54 ≤ 511279475705763 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2249R_270
#print axioms SieveCert.rows2249R_273
