/-
# Round 710: the refined certificate at `L = 899/400` with `n = 300`, parts 154–156 of 534

File 39 of 135: the parts `rows22475R_154` … `rows22475R_156` of `SieveCert22475R.lean`'s certificate on
`SieveGrid22475R.grid22475R` (3 parts, 22631 tests: row 76 columns 0–34, row 76 columns 35–57, row 76 columns
58–67), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows22475R_154 : rowsJ2 76 77 0 35 ≤ 529999379218700 := by decide +kernel

theorem rows22475R_155 : rowsJ2 76 77 35 58 ≤ 889375326505301 := by decide +kernel

theorem rows22475R_156 : rowsJ2 76 77 58 68 ≤ 91043290237141 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22475R_154
#print axioms SieveCert.rows22475R_156
