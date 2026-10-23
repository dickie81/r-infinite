/-
# Round 710: the refined certificate at `L = 2249/1000` with `n = 300`, parts 243–246 of 503

File 64 of 127: the parts `rows2249R_243` … `rows2249R_246` of `SieveCert2249R.lean`'s certificate on
`SieveGrid2249R.grid2249R` (4 parts, 28692 tests: row 92 columns 0–52, row 92 columns 53–60, row 92 columns 61–65,
row 92 columns 66–71), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one
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

theorem rows2249R_243 : rowsJ2 92 93 0 53 ≤ 631939035963987 := by decide +kernel

theorem rows2249R_244 : rowsJ2 92 93 53 61 ≤ 0 := by decide +kernel

theorem rows2249R_245 : rowsJ2 92 93 61 66 ≤ 0 := by decide +kernel

theorem rows2249R_246 : rowsJ2 92 93 66 72 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2249R_243
#print axioms SieveCert.rows2249R_246
