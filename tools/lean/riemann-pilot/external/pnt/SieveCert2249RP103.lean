/-
# Round 710: the refined certificate at `L = 2249/1000` with `n = 300`, parts 392–395 of 503

File 103 of 127: the parts `rows2249R_392` … `rows2249R_395` of `SieveCert2249R.lean`'s certificate on
`SieveGrid2249R.grid2249R` (4 parts, 29723 tests: row 123 columns 0–46, row 123 columns 47–55, row 123 columns
56–299, row 124 columns 0–46), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows2249R_392 : rowsJ2 123 124 0 47 ≤ 151747472533211 := by decide +kernel

theorem rows2249R_393 : rowsJ2 123 124 47 56 ≤ 55451543882128 := by decide +kernel

theorem rows2249R_394 : rowsJ2 123 124 56 300 ≤ 855071657950017 := by decide +kernel

theorem rows2249R_395 : rowsJ2 124 125 0 47 ≤ 147789102128666 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2249R_392
#print axioms SieveCert.rows2249R_395
