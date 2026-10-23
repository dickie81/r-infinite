/-
# Round 710: the refined certificate at `L = 899/400` with `n = 300`, parts 343–346 of 534

File 89 of 135: the parts `rows22475R_343` … `rows22475R_346` of `SieveCert22475R.lean`'s certificate on
`SieveGrid22475R.grid22475R` (4 parts, 28114 tests: row 106 columns 65–72, row 106 columns 73–299, row 107 columns
0–51, row 107 columns 52–58), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22475R_343 : rowsJ2 106 107 65 73 ≤ 1984564258289 := by decide +kernel

theorem rows22475R_344 : rowsJ2 106 107 73 300 ≤ 1033563118961386 := by decide +kernel

theorem rows22475R_345 : rowsJ2 107 108 0 52 ≤ 400704013993440 := by decide +kernel

theorem rows22475R_346 : rowsJ2 107 108 52 59 ≤ 26146606435018 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22475R_343
#print axioms SieveCert.rows22475R_346
