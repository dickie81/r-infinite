/-
# Round 710: the refined certificate at `L = 899/400` with `n = 300`, parts 103–106 of 534

File 26 of 135: the parts `rows22475R_103` … `rows22475R_106` of `SieveCert22475R.lean`'s certificate on
`SieveGrid22475R.grid22475R` (4 parts, 24574 tests: row 64 columns 0–34, row 64 columns 35–44, row 64 columns 45–60,
row 64 columns 61–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`,
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

theorem rows22475R_103 : rowsJ2 64 65 0 35 ≤ 876141720274976 := by decide +kernel

theorem rows22475R_104 : rowsJ2 64 65 35 45 ≤ 536172118423259 := by decide +kernel

theorem rows22475R_105 : rowsJ2 64 65 45 61 ≤ 773695716125597 := by decide +kernel

theorem rows22475R_106 : rowsJ2 64 65 61 300 ≤ 115734122040602 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22475R_103
#print axioms SieveCert.rows22475R_106
