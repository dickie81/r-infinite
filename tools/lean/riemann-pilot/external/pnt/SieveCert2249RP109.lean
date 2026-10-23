/-
# Round 710: the refined certificate at `L = 2249/1000` with `n = 300`, parts 417–421 of 503

File 109 of 127: the parts `rows2249R_417` … `rows2249R_421` of `SieveCert2249R.lean`'s certificate on
`SieveGrid2249R.grid2249R` (5 parts, 26591 tests: row 131 columns 45–56, row 131 columns 57–299, row 132 columns
0–44, row 132 columns 45–57, row 132 columns 58–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its
bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid2249R.lean`.
-/
import SieveGrid2249R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid2249R

theorem rows2249R_417 : rowsJ2 131 132 45 57 ≤ 45245375245124 := by decide +kernel

theorem rows2249R_418 : rowsJ2 131 132 57 300 ≤ 2132976607288888 := by decide +kernel

theorem rows2249R_419 : rowsJ2 132 133 0 45 ≤ 122625986822487 := by decide +kernel

theorem rows2249R_420 : rowsJ2 132 133 45 58 ≤ 40959587467517 := by decide +kernel

theorem rows2249R_421 : rowsJ2 132 133 58 300 ≤ 2282128234816720 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2249R_417
#print axioms SieveCert.rows2249R_421
