/-
# Round 710: the refined certificate at `L = 899/400` with `n = 300`, parts 268–271 of 534

File 69 of 135: the parts `rows22475R_268` … `rows22475R_271` of `SieveCert22475R.lean`'s certificate on
`SieveGrid22475R.grid22475R` (4 parts, 23295 tests: row 93 columns 66–70, row 93 columns 71–76, row 93 columns
77–84, row 93 columns 85–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22475R_268 : rowsJ2 93 94 66 71 ≤ 0 := by decide +kernel

theorem rows22475R_269 : rowsJ2 93 94 71 77 ≤ 4108233882694 := by decide +kernel

theorem rows22475R_270 : rowsJ2 93 94 77 85 ≤ 49414746229238 := by decide +kernel

theorem rows22475R_271 : rowsJ2 93 94 85 300 ≤ 1084431198753275 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22475R_268
#print axioms SieveCert.rows22475R_271
