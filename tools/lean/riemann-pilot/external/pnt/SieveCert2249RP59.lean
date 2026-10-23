/-
# Round 710: the refined certificate at `L = 2249/1000` with `n = 300`, parts 224–227 of 503

File 59 of 127: the parts `rows2249R_224` … `rows2249R_227` of `SieveCert2249R.lean`'s certificate on
`SieveGrid2249R.grid2249R` (4 parts, 24670 tests: row 88 columns 85–299, row 89 columns 0–51, row 89 columns 52–61,
row 89 columns 62–66), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one
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

theorem rows2249R_224 : rowsJ2 88 89 85 300 ≤ 215693407108787 := by decide +kernel

theorem rows2249R_225 : rowsJ2 89 90 0 52 ≤ 717649487870302 := by decide +kernel

theorem rows2249R_226 : rowsJ2 89 90 52 62 ≤ 2948129298075 := by decide +kernel

theorem rows2249R_227 : rowsJ2 89 90 62 67 ≤ 288584706811 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2249R_224
#print axioms SieveCert.rows2249R_227
