/-
# Round 710: the refined certificate at `L = 899/400` with `n = 300`, parts 59–62 of 534

File 15 of 135: the parts `rows22475R_59` … `rows22475R_62` of `SieveCert22475R.lean`'s certificate on
`SieveGrid22475R.grid22475R` (4 parts, 25368 tests: row 53 columns 0–34, row 53 columns 35–43, row 53 columns 44–50,
row 53 columns 51–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`,
one at a time (`Elab.async false`).

The file imports `SieveGrid22475R.lean`.
-/
import SieveGrid22475R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22475R

theorem rows22475R_59 : rowsJ2 53 54 0 35 ≤ 1564455114992086 := by decide +kernel

theorem rows22475R_60 : rowsJ2 53 54 35 44 ≤ 348250444205098 := by decide +kernel

theorem rows22475R_61 : rowsJ2 53 54 44 51 ≤ 504022105370828 := by decide +kernel

theorem rows22475R_62 : rowsJ2 53 54 51 300 ≤ 206607259676951 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22475R_59
#print axioms SieveCert.rows22475R_62
