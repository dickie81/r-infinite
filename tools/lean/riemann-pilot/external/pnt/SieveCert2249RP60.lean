/-
# Round 710: the refined certificate at `L = 2249/1000` with `n = 300`, parts 228–230 of 503

File 60 of 127: the parts `rows2249R_228` … `rows2249R_230` of `SieveCert2249R.lean`'s certificate on
`SieveGrid2249R.grid2249R` (3 parts, 22478 tests: row 89 columns 67–72, row 89 columns 73–79, row 89 columns
80–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
(`Elab.async false`).

The file imports `SieveGrid2249R.lean`.
-/
import SieveGrid2249R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid2249R

theorem rows2249R_228 : rowsJ2 89 90 67 73 ≤ 22636350487 := by decide +kernel

theorem rows2249R_229 : rowsJ2 89 90 73 80 ≤ 8782067242835 := by decide +kernel

theorem rows2249R_230 : rowsJ2 89 90 80 300 ≤ 502273417315824 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2249R_228
#print axioms SieveCert.rows2249R_230
