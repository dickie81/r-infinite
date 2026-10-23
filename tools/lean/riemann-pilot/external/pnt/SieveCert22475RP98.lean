/-
# Round 710: the refined certificate at `L = 899/400` with `n = 300`, parts 377–379 of 534

File 98 of 135: the parts `rows22475R_377` … `rows22475R_379` of `SieveCert22475R.lean`'s certificate on
`SieveGrid22475R.grid22475R` (3 parts, 22991 tests: row 113 columns 66–299, row 114 columns 0–50, row 114 columns
51–57), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
(`Elab.async false`).

The file imports `SieveGrid22475R.lean`.
-/
import SieveGrid22475R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22475R

theorem rows22475R_377 : rowsJ2 113 114 66 300 ≤ 561619906368040 := by decide +kernel

theorem rows22475R_378 : rowsJ2 114 115 0 51 ≤ 294882933107529 := by decide +kernel

theorem rows22475R_379 : rowsJ2 114 115 51 58 ≤ 47270863012523 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22475R_377
#print axioms SieveCert.rows22475R_379
