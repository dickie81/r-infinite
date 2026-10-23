/-
# Round 710: the refined certificate at `L = 2249/1000` with `n = 300`, parts 377–380 of 503

File 99 of 127: the parts `rows2249R_377` … `rows2249R_380` of `SieveCert2249R.lean`'s certificate on
`SieveGrid2249R.grid2249R` (4 parts, 24632 tests: row 119 columns 0–48, row 119 columns 49–56, row 119 columns
57–68, row 119 columns 69–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows2249R_377 : rowsJ2 119 120 0 49 ≤ 190309805230942 := by decide +kernel

theorem rows2249R_378 : rowsJ2 119 120 49 57 ≤ 49186784563002 := by decide +kernel

theorem rows2249R_379 : rowsJ2 119 120 57 69 ≤ 6160486210409 := by decide +kernel

theorem rows2249R_380 : rowsJ2 119 120 69 300 ≤ 209297219184391 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2249R_377
#print axioms SieveCert.rows2249R_380
