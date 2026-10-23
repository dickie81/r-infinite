/-
# Round 710: the refined certificate at `L = 2249/1000` with `n = 300`, parts 9–13 of 503

File 3 of 127: the parts `rows2249R_9` … `rows2249R_13` of `SieveCert2249R.lean`'s certificate on
`SieveGrid2249R.grid2249R` (5 parts, 29891 tests: rows 32–32, rows 33–33, rows 34–34, row 35 columns 0–34, row 35
columns 35–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a
time (`Elab.async false`).

The file imports `SieveGrid2249R.lean`.
-/
import SieveGrid2249R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid2249R

theorem rows2249R_9 : rows2 32 33 ≤ 2621737592057711 := by decide +kernel

theorem rows2249R_10 : rows2 33 34 ≤ 2665494297103090 := by decide +kernel

theorem rows2249R_11 : rows2 34 35 ≤ 2689260317610014 := by decide +kernel

theorem rows2249R_12 : rowsJ2 35 36 0 35 ≤ 2612797480010469 := by decide +kernel

theorem rows2249R_13 : rowsJ2 35 36 35 300 ≤ 81904171914107 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2249R_9
#print axioms SieveCert.rows2249R_13
