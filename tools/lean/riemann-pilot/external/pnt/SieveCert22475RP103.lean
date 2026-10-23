/-
# Round 710: the refined certificate at `L = 899/400` with `n = 300`, parts 396–399 of 534

File 103 of 135: the parts `rows22475R_396` … `rows22475R_399` of `SieveCert22475R.lean`'s certificate on
`SieveGrid22475R.grid22475R` (4 parts, 27357 tests: row 118 columns 56–64, row 118 columns 65–299, row 119 columns
0–48, row 119 columns 49–55), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22475R_396 : rowsJ2 118 119 56 65 ≤ 18856629227691 := by decide +kernel

theorem rows22475R_397 : rowsJ2 118 119 65 300 ≤ 333206717702280 := by decide +kernel

theorem rows22475R_398 : rowsJ2 119 120 0 49 ≤ 227248125293402 := by decide +kernel

theorem rows22475R_399 : rowsJ2 119 120 49 56 ≤ 56842823470901 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22475R_396
#print axioms SieveCert.rows22475R_399
