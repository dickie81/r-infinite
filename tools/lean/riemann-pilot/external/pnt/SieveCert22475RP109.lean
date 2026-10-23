/-
# Round 710: the refined certificate at `L = 899/400` with `n = 300`, parts 420–423 of 534

File 109 of 135: the parts `rows22475R_420` … `rows22475R_423` of `SieveCert22475R.lean`'s certificate on
`SieveGrid22475R.grid22475R` (4 parts, 23138 tests: row 124 columns 56–68, row 124 columns 69–299, row 125 columns
0–46, row 125 columns 47–54), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22475R_420 : rowsJ2 124 125 56 69 ≤ 7992955745177 := by decide +kernel

theorem rows22475R_421 : rowsJ2 124 125 69 300 ≤ 1044577443600241 := by decide +kernel

theorem rows22475R_422 : rowsJ2 125 126 0 47 ≤ 169355599342543 := by decide +kernel

theorem rows22475R_423 : rowsJ2 125 126 47 55 ≤ 62873040131614 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22475R_420
#print axioms SieveCert.rows22475R_423
