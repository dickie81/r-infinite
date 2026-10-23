/-
# Round 710: the refined certificate at `L = 2249/1000` with `n = 300`, parts 201–203 of 503

File 53 of 127: the parts `rows2249R_201` … `rows2249R_203` of `SieveCert2249R.lean`'s certificate on
`SieveGrid2249R.grid2249R` (3 parts, 22185 tests: row 85 columns 68–72, row 85 columns 73–78, row 85 columns
79–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows2249R_201 : rowsJ2 85 86 68 73 ≤ 1462148609116 := by decide +kernel

theorem rows2249R_202 : rowsJ2 85 86 73 79 ≤ 2079374849599 := by decide +kernel

theorem rows2249R_203 : rowsJ2 85 86 79 300 ≤ 29621312388247 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2249R_201
#print axioms SieveCert.rows2249R_203
