/-
# Round 710: the refined certificate at `L = 2249/1000` with `n = 300`, parts 308–311 of 503

File 81 of 127: the parts `rows2249R_308` … `rows2249R_311` of `SieveCert2249R.lean`'s certificate on
`SieveGrid2249R.grid2249R` (4 parts, 26785 tests: row 103 columns 60–66, row 103 columns 67–75, row 103 columns
76–299, row 104 columns 0–52), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows2249R_308 : rowsJ2 103 104 60 67 ≤ 0 := by decide +kernel

theorem rows2249R_309 : rowsJ2 103 104 67 76 ≤ 10298064089167 := by decide +kernel

theorem rows2249R_310 : rowsJ2 103 104 76 300 ≤ 1031179641695763 := by decide +kernel

theorem rows2249R_311 : rowsJ2 104 105 0 53 ≤ 380103239760935 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2249R_308
#print axioms SieveCert.rows2249R_311
