/-
# Round 710: the refined certificate at `L = 899/400` with `n = 300`, parts 67–70 of 534

File 17 of 135: the parts `rows22475R_67` … `rows22475R_70` of `SieveCert22475R.lean`'s certificate on
`SieveGrid22475R.grid22475R` (4 parts, 26156 tests: row 55 columns 0–34, row 55 columns 35–43, row 55 columns 44–51,
row 55 columns 52–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`,
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

theorem rows22475R_67 : rowsJ2 55 56 0 35 ≤ 1422576936029494 := by decide +kernel

theorem rows22475R_68 : rowsJ2 55 56 35 44 ≤ 353142908278904 := by decide +kernel

theorem rows22475R_69 : rowsJ2 55 56 44 52 ≤ 568161373565366 := by decide +kernel

theorem rows22475R_70 : rowsJ2 55 56 52 300 ≤ 251571361289325 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22475R_67
#print axioms SieveCert.rows22475R_70
