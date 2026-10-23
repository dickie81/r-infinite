/-
# Round 710: the refined certificate at `L = 2249/1000` with `n = 300`, parts 212–215 of 503

File 56 of 127: the parts `rows2249R_212` … `rows2249R_215` of `SieveCert2249R.lean`'s certificate on
`SieveGrid2249R.grid2249R` (4 parts, 28094 tests: row 87 columns 43–61, row 87 columns 62–66, row 87 columns 67–71,
row 87 columns 72–77), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one
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

theorem rows2249R_212 : rowsJ2 87 88 43 62 ≤ 107971634821605 := by decide +kernel

theorem rows2249R_213 : rowsJ2 87 88 62 67 ≤ 782403864130 := by decide +kernel

theorem rows2249R_214 : rowsJ2 87 88 67 72 ≤ 503383742479 := by decide +kernel

theorem rows2249R_215 : rowsJ2 87 88 72 78 ≤ 1975223119237 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2249R_212
#print axioms SieveCert.rows2249R_215
