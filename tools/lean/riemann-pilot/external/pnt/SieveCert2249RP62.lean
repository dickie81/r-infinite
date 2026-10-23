/-
# Round 710: the refined certificate at `L = 2249/1000` with `n = 300`, parts 235–238 of 503

File 62 of 127: the parts `rows2249R_235` … `rows2249R_238` of `SieveCert2249R.lean`'s certificate on
`SieveGrid2249R.grid2249R` (4 parts, 29605 tests: row 90 columns 73–79, row 90 columns 80–299, row 91 columns 0–52,
row 91 columns 53–61), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one
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

theorem rows2249R_235 : rowsJ2 90 91 73 80 ≤ 10287585880146 := by decide +kernel

theorem rows2249R_236 : rowsJ2 90 91 80 300 ≤ 629318249918891 := by decide +kernel

theorem rows2249R_237 : rowsJ2 91 92 0 53 ≤ 660779036689547 := by decide +kernel

theorem rows2249R_238 : rowsJ2 91 92 53 62 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2249R_235
#print axioms SieveCert.rows2249R_238
