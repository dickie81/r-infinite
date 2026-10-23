/-
# Round 710: the refined certificate at `L = 2249/1000` with `n = 300`, parts 169–172 of 503

File 45 of 127: the parts `rows2249R_169` … `rows2249R_172` of `SieveCert2249R.lean`'s certificate on
`SieveGrid2249R.grid2249R` (4 parts, 29026 tests: row 80 columns 36–61, row 80 columns 62–67, row 80 columns 68–72,
row 80 columns 73–77), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one
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

theorem rows2249R_169 : rowsJ2 80 81 36 62 ≤ 536323133120448 := by decide +kernel

theorem rows2249R_170 : rowsJ2 80 81 62 68 ≤ 3559432547925 := by decide +kernel

theorem rows2249R_171 : rowsJ2 80 81 68 73 ≤ 8090101318113 := by decide +kernel

theorem rows2249R_172 : rowsJ2 80 81 73 78 ≤ 4461033890657 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2249R_169
#print axioms SieveCert.rows2249R_172
