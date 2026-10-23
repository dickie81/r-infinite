/-
# Round 710: the refined certificate at `L = 2249/1000` with `n = 300`, parts 323–326 of 503

File 85 of 127: the parts `rows2249R_323` … `rows2249R_326` of `SieveCert2249R.lean`'s certificate on
`SieveGrid2249R.grid2249R` (4 parts, 25178 tests: row 106 columns 59–65, row 106 columns 66–75, row 106 columns
76–299, row 107 columns 0–51), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows2249R_323 : rowsJ2 106 107 59 66 ≤ 1327145430467 := by decide +kernel

theorem rows2249R_324 : rowsJ2 106 107 66 76 ≤ 12972740780788 := by decide +kernel

theorem rows2249R_325 : rowsJ2 106 107 76 300 ≤ 781969117108225 := by decide +kernel

theorem rows2249R_326 : rowsJ2 107 108 0 52 ≤ 332476162043849 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2249R_323
#print axioms SieveCert.rows2249R_326
