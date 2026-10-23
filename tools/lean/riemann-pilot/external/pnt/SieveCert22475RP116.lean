/-
# Round 710: the refined certificate at `L = 899/400` with `n = 300`, parts 448–452 of 534

File 116 of 135: the parts `rows22475R_448` … `rows22475R_452` of `SieveCert22475R.lean`'s certificate on
`SieveGrid22475R.grid22475R` (5 parts, 27905 tests: row 133 columns 45–55, row 133 columns 56–299, row 134 columns
0–43, row 134 columns 44–54, row 134 columns 55–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its
bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22475R.lean`.
-/
import SieveGrid22475R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22475R

theorem rows22475R_448 : rowsJ2 133 134 45 56 ≤ 57199867053667 := by decide +kernel

theorem rows22475R_449 : rowsJ2 133 134 56 300 ≤ 2462429443080063 := by decide +kernel

theorem rows22475R_450 : rowsJ2 134 135 0 44 ≤ 125843588037703 := by decide +kernel

theorem rows22475R_451 : rowsJ2 134 135 44 55 ≤ 64195299353256 := by decide +kernel

theorem rows22475R_452 : rowsJ2 134 135 55 300 ≤ 2462001150770146 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22475R_448
#print axioms SieveCert.rows22475R_452
