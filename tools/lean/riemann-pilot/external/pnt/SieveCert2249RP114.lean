/-
# Round 710: the refined certificate at `L = 2249/1000` with `n = 300`, parts 438–441 of 503

File 114 of 127: the parts `rows2249R_438` … `rows2249R_441` of `SieveCert2249R.lean`'s certificate on
`SieveGrid2249R.grid2249R` (4 parts, 25367 tests: row 140 columns 0–41, row 140 columns 42–299, row 141 columns
0–41, row 141 columns 42–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows2249R_438 : rowsJ2 140 141 0 42 ≤ 121643133104153 := by decide +kernel

theorem rows2249R_439 : rowsJ2 140 141 42 300 ≤ 2383291160065240 := by decide +kernel

theorem rows2249R_440 : rowsJ2 141 142 0 42 ≤ 128305516436792 := by decide +kernel

theorem rows2249R_441 : rowsJ2 141 142 42 300 ≤ 2384283129058057 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2249R_438
#print axioms SieveCert.rows2249R_441
