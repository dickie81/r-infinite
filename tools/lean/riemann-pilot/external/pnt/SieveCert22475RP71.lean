/-
# Round 710: the refined certificate at `L = 899/400` with `n = 300`, parts 276–279 of 534

File 71 of 135: the parts `rows22475R_276` … `rows22475R_279` of `SieveCert22475R.lean`'s certificate on
`SieveGrid22475R.grid22475R` (4 parts, 28920 tests: row 94 columns 72–78, row 94 columns 79–299, row 95 columns
0–52, row 95 columns 53–60), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22475R_276 : rowsJ2 94 95 72 79 ≤ 11342323060310 := by decide +kernel

theorem rows22475R_277 : rowsJ2 94 95 79 300 ≤ 1355571669607893 := by decide +kernel

theorem rows22475R_278 : rowsJ2 95 96 0 53 ≤ 662336422952010 := by decide +kernel

theorem rows22475R_279 : rowsJ2 95 96 53 61 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22475R_276
#print axioms SieveCert.rows22475R_279
