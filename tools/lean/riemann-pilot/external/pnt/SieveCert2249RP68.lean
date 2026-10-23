/-
# Round 710: the refined certificate at `L = 2249/1000` with `n = 300`, parts 259–262 of 503

File 68 of 127: the parts `rows2249R_259` … `rows2249R_262` of `SieveCert2249R.lean`'s certificate on
`SieveGrid2249R.grid2249R` (4 parts, 27620 tests: row 94 columns 72–78, row 94 columns 79–299, row 95 columns 0–53,
row 95 columns 54–60), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one
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

theorem rows2249R_259 : rowsJ2 94 95 72 79 ≤ 12726414027457 := by decide +kernel

theorem rows2249R_260 : rowsJ2 94 95 79 300 ≤ 1314461854072210 := by decide +kernel

theorem rows2249R_261 : rowsJ2 95 96 0 54 ≤ 556496146622434 := by decide +kernel

theorem rows2249R_262 : rowsJ2 95 96 54 61 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2249R_259
#print axioms SieveCert.rows2249R_262
