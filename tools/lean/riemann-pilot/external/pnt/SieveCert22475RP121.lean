/-
# Round 710: the refined certificate at `L = 899/400` with `n = 300`, parts 468–471 of 534

File 121 of 135: the parts `rows22475R_468` … `rows22475R_471` of `SieveCert22475R.lean`'s certificate on
`SieveGrid22475R.grid22475R` (4 parts, 27693 tests: row 141 columns 42–299, row 142 columns 0–41, row 142 columns
42–299, row 143 columns 0–41), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22475R_468 : rowsJ2 141 142 42 300 ≤ 2500028879920696 := by decide +kernel

theorem rows22475R_469 : rowsJ2 142 143 0 42 ≤ 134902741142090 := by decide +kernel

theorem rows22475R_470 : rowsJ2 142 143 42 300 ≤ 2500074808944688 := by decide +kernel

theorem rows22475R_471 : rowsJ2 143 144 0 42 ≤ 140854850755435 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22475R_468
#print axioms SieveCert.rows22475R_471
