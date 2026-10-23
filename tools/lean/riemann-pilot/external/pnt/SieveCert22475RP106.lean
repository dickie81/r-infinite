/-
# Round 710: the refined certificate at `L = 899/400` with `n = 300`, parts 408–411 of 534

File 106 of 135: the parts `rows22475R_408` … `rows22475R_411` of `SieveCert22475R.lean`'s certificate on
`SieveGrid22475R.grid22475R` (4 parts, 24906 tests: row 121 columns 57–67, row 121 columns 68–299, row 122 columns
0–47, row 122 columns 48–55), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22475R_408 : rowsJ2 121 122 57 68 ≤ 9230846827361 := by decide +kernel

theorem rows22475R_409 : rowsJ2 121 122 68 300 ≤ 605138145635927 := by decide +kernel

theorem rows22475R_410 : rowsJ2 122 123 0 48 ≤ 196246862420968 := by decide +kernel

theorem rows22475R_411 : rowsJ2 122 123 48 56 ≤ 63047781618889 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22475R_408
#print axioms SieveCert.rows22475R_411
