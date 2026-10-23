/-
# Round 710: the refined certificate at `L = 899/400` with `n = 300`, parts 304–307 of 534

File 78 of 135: the parts `rows22475R_304` … `rows22475R_307` of `SieveCert22475R.lean`'s certificate on
`SieveGrid22475R.grid22475R` (4 parts, 25945 tests: row 99 columns 60–64, row 99 columns 65–70, row 99 columns
71–78, row 99 columns 79–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22475R_304 : rowsJ2 99 100 60 65 ≤ 0 := by decide +kernel

theorem rows22475R_305 : rowsJ2 99 100 65 71 ≤ 0 := by decide +kernel

theorem rows22475R_306 : rowsJ2 99 100 71 79 ≤ 19737901082264 := by decide +kernel

theorem rows22475R_307 : rowsJ2 99 100 79 300 ≤ 1448413745483183 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22475R_304
#print axioms SieveCert.rows22475R_307
