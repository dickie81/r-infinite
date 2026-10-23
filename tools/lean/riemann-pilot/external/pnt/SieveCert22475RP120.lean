/-
# Round 710: the refined certificate at `L = 899/400` with `n = 300`, parts 464–467 of 534

File 120 of 135: the parts `rows22475R_464` … `rows22475R_467` of `SieveCert22475R.lean`'s certificate on
`SieveGrid22475R.grid22475R` (4 parts, 28978 tests: row 139 columns 43–299, row 140 columns 0–42, row 140 columns
43–299, row 141 columns 0–41), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22475R_464 : rowsJ2 139 140 43 300 ≤ 2500517350111667 := by decide +kernel

theorem rows22475R_465 : rowsJ2 140 141 0 43 ≤ 135269153060361 := by decide +kernel

theorem rows22475R_466 : rowsJ2 140 141 43 300 ≤ 2498539911119355 := by decide +kernel

theorem rows22475R_467 : rowsJ2 141 142 0 42 ≤ 128325911262933 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22475R_464
#print axioms SieveCert.rows22475R_467
