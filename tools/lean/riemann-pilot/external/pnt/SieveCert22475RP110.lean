/-
# Round 710: the refined certificate at `L = 899/400` with `n = 300`, parts 424–427 of 534

File 110 of 135: the parts `rows22475R_424` … `rows22475R_427` of `SieveCert22475R.lean`'s certificate on
`SieveGrid22475R.grid22475R` (4 parts, 24033 tests: row 125 columns 55–67, row 125 columns 68–299, row 126 columns
0–46, row 126 columns 47–55), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22475R_424 : rowsJ2 125 126 55 68 ≤ 9890759998053 := by decide +kernel

theorem rows22475R_425 : rowsJ2 125 126 68 300 ≤ 1222025393533847 := by decide +kernel

theorem rows22475R_426 : rowsJ2 126 127 0 47 ≤ 166227277416589 := by decide +kernel

theorem rows22475R_427 : rowsJ2 126 127 47 56 ≤ 63092438642878 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22475R_424
#print axioms SieveCert.rows22475R_427
