/-
# Round 710: the refined certificate at `L = 2249/1000` with `n = 300`, parts 247–250 of 503

File 65 of 127: the parts `rows2249R_247` … `rows2249R_250` of `SieveCert2249R.lean`'s certificate on
`SieveGrid2249R.grid2249R` (4 parts, 29832 tests: row 92 columns 72–78, row 92 columns 79–299, row 93 columns 0–53,
row 93 columns 54–61), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one
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

theorem rows2249R_247 : rowsJ2 92 93 72 79 ≤ 9728978394616 := by decide +kernel

theorem rows2249R_248 : rowsJ2 92 93 79 300 ≤ 988233604871539 := by decide +kernel

theorem rows2249R_249 : rowsJ2 93 94 0 54 ≤ 606354932309919 := by decide +kernel

theorem rows2249R_250 : rowsJ2 93 94 54 62 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2249R_247
#print axioms SieveCert.rows2249R_250
