/-
# Round 710: the refined certificate at `L = 899/400` with `n = 300`, parts 359–362 of 534

File 93 of 135: the parts `rows22475R_359` … `rows22475R_362` of `SieveCert22475R.lean`'s certificate on
`SieveGrid22475R.grid22475R` (4 parts, 25448 tests: row 109 columns 74–299, row 110 columns 0–51, row 110 columns
52–57, row 110 columns 58–64), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
+kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22475R.lean`.
-/
import SieveGrid22475R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22475R

theorem rows22475R_359 : rowsJ2 109 110 74 300 ≤ 786477898602078 := by decide +kernel

theorem rows22475R_360 : rowsJ2 110 111 0 52 ≤ 354086802108101 := by decide +kernel

theorem rows22475R_361 : rowsJ2 110 111 52 58 ≤ 32513363907810 := by decide +kernel

theorem rows22475R_362 : rowsJ2 110 111 58 65 ≤ 12860737576111 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22475R_359
#print axioms SieveCert.rows22475R_362
