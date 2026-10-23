/-
# Round 710: the refined certificate at `L = 899/400` with `n = 300`, parts 55–58 of 534

File 14 of 135: the parts `rows22475R_55` … `rows22475R_58` of `SieveCert22475R.lean`'s certificate on
`SieveGrid22475R.grid22475R` (4 parts, 24780 tests: row 52 columns 0–34, row 52 columns 35–43, row 52 columns 44–50,
row 52 columns 51–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`,
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

theorem rows22475R_55 : rowsJ2 52 53 0 35 ≤ 1637094108330257 := by decide +kernel

theorem rows22475R_56 : rowsJ2 52 53 35 44 ≤ 349986912229283 := by decide +kernel

theorem rows22475R_57 : rowsJ2 52 53 44 51 ≤ 504531266603894 := by decide +kernel

theorem rows22475R_58 : rowsJ2 52 53 51 300 ≤ 142792530334703 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22475R_55
#print axioms SieveCert.rows22475R_58
