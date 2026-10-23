/-
# Round 710: the refined certificate at `L = 2249/1000` with `n = 300`, parts 125–128 of 503

File 33 of 127: the parts `rows2249R_125` … `rows2249R_128` of `SieveCert2249R.lean`'s certificate on
`SieveGrid2249R.grid2249R` (4 parts, 27714 tests: row 71 columns 0–34, row 71 columns 35–50, row 71 columns 51–67,
row 71 columns 68–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`,
one at a time (`Elab.async false`).

The file imports `SieveGrid2249R.lean`.
-/
import SieveGrid2249R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid2249R

theorem rows2249R_125 : rowsJ2 71 72 0 35 ≤ 526809515706299 := by decide +kernel

theorem rows2249R_126 : rowsJ2 71 72 35 51 ≤ 751812300071652 := by decide +kernel

theorem rows2249R_127 : rowsJ2 71 72 51 68 ≤ 293322784466189 := by decide +kernel

theorem rows2249R_128 : rowsJ2 71 72 68 300 ≤ 21098303904601 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2249R_125
#print axioms SieveCert.rows2249R_128
