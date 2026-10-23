/-
# Round 710: the refined certificate at `L = 2249/1000` with `n = 300`, parts 338–341 of 503

File 89 of 127: the parts `rows2249R_338` … `rows2249R_341` of `SieveCert2249R.lean`'s certificate on
`SieveGrid2249R.grid2249R` (4 parts, 23168 tests: row 109 columns 58–65, row 109 columns 66–80, row 109 columns
81–299, row 110 columns 0–50), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
+kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid2249R.lean`.
-/
import SieveGrid2249R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid2249R

theorem rows2249R_338 : rowsJ2 109 110 58 66 ≤ 7159070237386 := by decide +kernel

theorem rows2249R_339 : rowsJ2 109 110 66 81 ≤ 463381825651120 := by decide +kernel

theorem rows2249R_340 : rowsJ2 109 110 81 300 ≤ 207221606181264 := by decide +kernel

theorem rows2249R_341 : rowsJ2 110 111 0 51 ≤ 286701600382665 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2249R_338
#print axioms SieveCert.rows2249R_341
