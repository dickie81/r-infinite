/-
# Round 710: the refined certificate at `L = 899/400` with `n = 300`, parts 87–90 of 534

File 22 of 135: the parts `rows22475R_87` … `rows22475R_90` of `SieveCert22475R.lean`'s certificate on
`SieveGrid22475R.grid22475R` (4 parts, 26094 tests: row 60 columns 0–34, row 60 columns 35–43, row 60 columns 44–53,
row 60 columns 54–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`,
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

theorem rows22475R_87 : rowsJ2 60 61 0 35 ≤ 1096778873866746 := by decide +kernel

theorem rows22475R_88 : rowsJ2 60 61 35 44 ≤ 412990538478715 := by decide +kernel

theorem rows22475R_89 : rowsJ2 60 61 44 54 ≤ 630608250266575 := by decide +kernel

theorem rows22475R_90 : rowsJ2 60 61 54 300 ≤ 331791376088053 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22475R_87
#print axioms SieveCert.rows22475R_90
