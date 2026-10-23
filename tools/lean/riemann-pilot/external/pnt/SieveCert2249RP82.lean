/-
# Round 710: the refined certificate at `L = 2249/1000` with `n = 300`, parts 312–315 of 503

File 82 of 127: the parts `rows2249R_312` … `rows2249R_315` of `SieveCert2249R.lean`'s certificate on
`SieveGrid2249R.grid2249R` (4 parts, 26274 tests: row 104 columns 53–58, row 104 columns 59–65, row 104 columns
66–74, row 104 columns 75–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows2249R_312 : rowsJ2 104 105 53 59 ≤ 10403434146145 := by decide +kernel

theorem rows2249R_313 : rowsJ2 104 105 59 66 ≤ 0 := by decide +kernel

theorem rows2249R_314 : rowsJ2 104 105 66 75 ≤ 6880496258910 := by decide +kernel

theorem rows2249R_315 : rowsJ2 104 105 75 300 ≤ 915442309537955 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2249R_312
#print axioms SieveCert.rows2249R_315
