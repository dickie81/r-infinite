/-
# Round 710: the refined certificate at `L = 2249/1000` with `n = 300`, parts 121–124 of 503

File 32 of 127: the parts `rows2249R_121` … `rows2249R_124` of `SieveCert2249R.lean`'s certificate on
`SieveGrid2249R.grid2249R` (4 parts, 26254 tests: row 70 columns 0–34, row 70 columns 35–49, row 70 columns 50–67,
row 70 columns 68–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`,
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

theorem rows2249R_121 : rowsJ2 70 71 0 35 ≤ 542259934002982 := by decide +kernel

theorem rows2249R_122 : rowsJ2 70 71 35 50 ≤ 737292876672909 := by decide +kernel

theorem rows2249R_123 : rowsJ2 70 71 50 68 ≤ 355250838593193 := by decide +kernel

theorem rows2249R_124 : rowsJ2 70 71 68 300 ≤ 19349023508926 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2249R_121
#print axioms SieveCert.rows2249R_124
