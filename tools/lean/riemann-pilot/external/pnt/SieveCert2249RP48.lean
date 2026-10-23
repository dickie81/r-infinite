/-
# Round 710: the refined certificate at `L = 2249/1000` with `n = 300`, parts 181–184 of 503

File 48 of 127: the parts `rows2249R_181` … `rows2249R_184` of `SieveCert2249R.lean`'s certificate on
`SieveGrid2249R.grid2249R` (4 parts, 28725 tests: row 82 columns 37–62, row 82 columns 63–67, row 82 columns 68–72,
row 82 columns 73–77), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one
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

theorem rows2249R_181 : rowsJ2 82 83 37 63 ≤ 414533443505374 := by decide +kernel

theorem rows2249R_182 : rowsJ2 82 83 63 68 ≤ 2345698846650 := by decide +kernel

theorem rows2249R_183 : rowsJ2 82 83 68 73 ≤ 4967628194779 := by decide +kernel

theorem rows2249R_184 : rowsJ2 82 83 73 78 ≤ 2118247761181 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2249R_181
#print axioms SieveCert.rows2249R_184
