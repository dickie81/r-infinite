/-
# Round 710: the refined certificate at `L = 2249/1000` with `n = 300`, parts 451–456 of 503

File 117 of 127: the parts `rows2249R_451` … `rows2249R_456` of `SieveCert2249R.lean`'s certificate on
`SieveGrid2249R.grid2249R` (6 parts, 29928 tests: row 146 columns 41–299, row 147 columns 0–40, row 147 columns
41–299, row 148 columns 0–40, row 148 columns 41–299, row 149 columns 0–40), each a sum of refined costs (`rows2` or
`rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid2249R.lean`.
-/
import SieveGrid2249R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid2249R

theorem rows2249R_451 : rowsJ2 146 147 41 300 ≤ 2402533913722262 := by decide +kernel

theorem rows2249R_452 : rowsJ2 147 148 0 41 ≤ 159295306118869 := by decide +kernel

theorem rows2249R_453 : rowsJ2 147 148 41 300 ≤ 2404764773151005 := by decide +kernel

theorem rows2249R_454 : rowsJ2 148 149 0 41 ≤ 164858652735031 := by decide +kernel

theorem rows2249R_455 : rowsJ2 148 149 41 300 ≤ 2409060521915904 := by decide +kernel

theorem rows2249R_456 : rowsJ2 149 150 0 41 ≤ 172052726820150 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2249R_451
#print axioms SieveCert.rows2249R_456
