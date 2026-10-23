/-
# Round 710: the refined certificate at `L = 2249/1000` with `n = 300`, parts 457–463 of 503

File 118 of 127: the parts `rows2249R_457` … `rows2249R_463` of `SieveCert2249R.lean`'s certificate on
`SieveGrid2249R.grid2249R` (7 parts, 26587 tests: row 149 columns 41–299, row 150 columns 0–40, row 150 columns
41–299, row 151 columns 0–92, row 151 columns 93–299, row 152 columns 0–108, row 152 columns 109–299), each a sum of
refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid2249R.lean`.
-/
import SieveGrid2249R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid2249R

theorem rows2249R_457 : rowsJ2 149 150 41 300 ≤ 2414805349311991 := by decide +kernel

theorem rows2249R_458 : rowsJ2 150 151 0 41 ≤ 177109658249838 := by decide +kernel

theorem rows2249R_459 : rowsJ2 150 151 41 300 ≤ 2422634769899483 := by decide +kernel

theorem rows2249R_460 : rowsJ2 151 152 0 93 ≤ 763041371580206 := by decide +kernel

theorem rows2249R_461 : rowsJ2 151 152 93 300 ≤ 1853531137320045 := by decide +kernel

theorem rows2249R_462 : rowsJ2 152 153 0 109 ≤ 2211984579095040 := by decide +kernel

theorem rows2249R_463 : rowsJ2 152 153 109 300 ≤ 421250449894481 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2249R_457
#print axioms SieveCert.rows2249R_463
