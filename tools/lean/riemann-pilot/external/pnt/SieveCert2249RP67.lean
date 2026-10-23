/-
# Round 710: the refined certificate at `L = 2249/1000` with `n = 300`, parts 255–258 of 503

File 67 of 127: the parts `rows2249R_255` … `rows2249R_258` of `SieveCert2249R.lean`'s certificate on
`SieveGrid2249R.grid2249R` (4 parts, 28650 tests: row 94 columns 0–53, row 94 columns 54–60, row 94 columns 61–65,
row 94 columns 66–71), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one
at a time (`Elab.async false`).

The file imports `SieveGrid2249R.lean`.
-/
import SieveGrid2249R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid2249R

theorem rows2249R_255 : rowsJ2 94 95 0 54 ≤ 579638574726112 := by decide +kernel

theorem rows2249R_256 : rowsJ2 94 95 54 61 ≤ 0 := by decide +kernel

theorem rows2249R_257 : rowsJ2 94 95 61 66 ≤ 0 := by decide +kernel

theorem rows2249R_258 : rowsJ2 94 95 66 72 ≤ 72550401414 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2249R_255
#print axioms SieveCert.rows2249R_258
