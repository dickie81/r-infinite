/-
# Round 710: the refined certificate at `L = 2249/1000` with `n = 300`, parts 193–196 of 503

File 51 of 127: the parts `rows2249R_193` … `rows2249R_196` of `SieveCert2249R.lean`'s certificate on
`SieveGrid2249R.grid2249R` (4 parts, 29789 tests: row 84 columns 38–62, row 84 columns 63–67, row 84 columns 68–72,
row 84 columns 73–78), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one
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

theorem rows2249R_193 : rowsJ2 84 85 38 63 ≤ 309038270553576 := by decide +kernel

theorem rows2249R_194 : rowsJ2 84 85 63 68 ≤ 2019054235403 := by decide +kernel

theorem rows2249R_195 : rowsJ2 84 85 68 73 ≤ 2395547146920 := by decide +kernel

theorem rows2249R_196 : rowsJ2 84 85 73 79 ≤ 1783464225460 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2249R_193
#print axioms SieveCert.rows2249R_196
