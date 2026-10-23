/-
# Round 710: the refined certificate at `L = 2249/1000` with `n = 300`, parts 301–303 of 503

File 79 of 127: the parts `rows2249R_301` … `rows2249R_303` of `SieveCert2249R.lean`'s certificate on
`SieveGrid2249R.grid2249R` (3 parts, 23327 tests: row 102 columns 0–52, row 102 columns 53–59, row 102 columns
60–66), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows2249R_301 : rowsJ2 102 103 0 53 ≤ 413714310185388 := by decide +kernel

theorem rows2249R_302 : rowsJ2 102 103 53 60 ≤ 4436552199851 := by decide +kernel

theorem rows2249R_303 : rowsJ2 102 103 60 67 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2249R_301
#print axioms SieveCert.rows2249R_303
