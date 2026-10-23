/-
# Round 710: the refined certificate at `L = 2249/1000` with `n = 300`, parts 396–399 of 503

File 104 of 127: the parts `rows2249R_396` … `rows2249R_399` of `SieveCert2249R.lean`'s certificate on
`SieveGrid2249R.grid2249R` (4 parts, 29893 tests: row 124 columns 47–55, row 124 columns 56–299, row 125 columns
0–46, row 125 columns 47–56), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows2249R_396 : rowsJ2 124 125 47 56 ≤ 51455062711032 := by decide +kernel

theorem rows2249R_397 : rowsJ2 124 125 56 300 ≤ 1032679589561623 := by decide +kernel

theorem rows2249R_398 : rowsJ2 125 126 0 47 ≤ 146948364367015 := by decide +kernel

theorem rows2249R_399 : rowsJ2 125 126 47 57 ≤ 49012729789099 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2249R_396
#print axioms SieveCert.rows2249R_399
