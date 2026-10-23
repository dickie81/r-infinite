/-
# Round 710: the refined certificate at `L = 899/400` with `n = 300`, parts 440–443 of 534

File 114 of 135: the parts `rows22475R_440` … `rows22475R_443` of `SieveCert22475R.lean`'s certificate on
`SieveGrid22475R.grid22475R` (4 parts, 23594 tests: row 130 columns 56–299, row 131 columns 0–44, row 131 columns
45–54, row 131 columns 55–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22475R_440 : rowsJ2 130 131 56 300 ≤ 2020398360174682 := by decide +kernel

theorem rows22475R_441 : rowsJ2 131 132 0 45 ≤ 134153046744504 := by decide +kernel

theorem rows22475R_442 : rowsJ2 131 132 45 55 ≤ 65487862285955 := by decide +kernel

theorem rows22475R_443 : rowsJ2 131 132 55 300 ≤ 2174070246351062 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22475R_440
#print axioms SieveCert.rows22475R_443
