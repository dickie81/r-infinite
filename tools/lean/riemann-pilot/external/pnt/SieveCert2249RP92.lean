/-
# Round 710: the refined certificate at `L = 2249/1000` with `n = 300`, parts 349–352 of 503

File 92 of 127: the parts `rows2249R_349` … `rows2249R_352` of `SieveCert2249R.lean`'s certificate on
`SieveGrid2249R.grid2249R` (4 parts, 28913 tests: row 112 columns 0–50, row 112 columns 51–57, row 112 columns
58–66, row 112 columns 67–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows2249R_349 : rowsJ2 112 113 0 51 ≤ 263418750173488 := by decide +kernel

theorem rows2249R_350 : rowsJ2 112 113 51 58 ≤ 38146283954871 := by decide +kernel

theorem rows2249R_351 : rowsJ2 112 113 58 67 ≤ 9622587822699 := by decide +kernel

theorem rows2249R_352 : rowsJ2 112 113 67 300 ≤ 448456777099493 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2249R_349
#print axioms SieveCert.rows2249R_352
