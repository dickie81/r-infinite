/-
# Round 710: the refined certificate at `L = 899/400` with `n = 300`, parts 83–86 of 534

File 21 of 135: the parts `rows22475R_83` … `rows22475R_86` of `SieveCert22475R.lean`'s certificate on
`SieveGrid22475R.grid22475R` (4 parts, 26300 tests: row 59 columns 0–34, row 59 columns 35–43, row 59 columns 44–52,
row 59 columns 53–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`,
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

theorem rows22475R_83 : rowsJ2 59 60 0 35 ≤ 1158151055284956 := by decide +kernel

theorem rows22475R_84 : rowsJ2 59 60 35 44 ≤ 396045646250658 := by decide +kernel

theorem rows22475R_85 : rowsJ2 59 60 44 53 ≤ 590910912266462 := by decide +kernel

theorem rows22475R_86 : rowsJ2 59 60 53 300 ≤ 358317734632057 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22475R_83
#print axioms SieveCert.rows22475R_86
