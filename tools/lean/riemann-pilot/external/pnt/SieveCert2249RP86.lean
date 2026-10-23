/-
# Round 710: the refined certificate at `L = 2249/1000` with `n = 300`, parts 327–330 of 503

File 86 of 127: the parts `rows2249R_327` … `rows2249R_330` of `SieveCert2249R.lean`'s certificate on
`SieveGrid2249R.grid2249R` (4 parts, 24350 tests: row 107 columns 52–58, row 107 columns 59–65, row 107 columns
66–75, row 107 columns 76–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows2249R_327 : rowsJ2 107 108 52 59 ≤ 23604731600568 := by decide +kernel

theorem rows2249R_328 : rowsJ2 107 108 59 66 ≤ 2433562213735 := by decide +kernel

theorem rows2249R_329 : rowsJ2 107 108 66 76 ≤ 14115987008044 := by decide +kernel

theorem rows2249R_330 : rowsJ2 107 108 76 300 ≤ 772538609302446 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2249R_327
#print axioms SieveCert.rows2249R_330
