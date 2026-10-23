/-
# Round 710: the refined certificate at `L = 899/400` with `n = 300`, parts 432–435 of 534

File 112 of 135: the parts `rows22475R_432` … `rows22475R_435` of `SieveCert22475R.lean`'s certificate on
`SieveGrid22475R.grid22475R` (4 parts, 28710 tests: row 128 columns 0–45, row 128 columns 46–54, row 128 columns
55–299, row 129 columns 0–45), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22475R_432 : rowsJ2 128 129 0 46 ≤ 149367763199177 := by decide +kernel

theorem rows22475R_433 : rowsJ2 128 129 46 55 ≤ 65420264282341 := by decide +kernel

theorem rows22475R_434 : rowsJ2 128 129 55 300 ≤ 1721596195751496 := by decide +kernel

theorem rows22475R_435 : rowsJ2 129 130 0 46 ≤ 147494656566860 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22475R_432
#print axioms SieveCert.rows22475R_435
