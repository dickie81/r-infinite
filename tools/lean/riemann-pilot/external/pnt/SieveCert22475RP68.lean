/-
# Round 710: the refined certificate at `L = 899/400` with `n = 300`, parts 263–267 of 534

File 68 of 135: the parts `rows22475R_263` … `rows22475R_267` of `SieveCert22475R.lean`'s certificate on
`SieveGrid22475R.grid22475R` (5 parts, 29850 tests: row 92 columns 78–86, row 92 columns 87–299, row 93 columns
0–51, row 93 columns 52–60, row 93 columns 61–65), each a sum of refined costs (`rows2` or `rowsJ2`) at most its
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

theorem rows22475R_263 : rowsJ2 92 93 78 87 ≤ 191330256444411 := by decide +kernel

theorem rows22475R_264 : rowsJ2 92 93 87 300 ≤ 827339021834986 := by decide +kernel

theorem rows22475R_265 : rowsJ2 93 94 0 52 ≤ 720182046647825 := by decide +kernel

theorem rows22475R_266 : rowsJ2 93 94 52 61 ≤ 1263667586625 := by decide +kernel

theorem rows22475R_267 : rowsJ2 93 94 61 66 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22475R_263
#print axioms SieveCert.rows22475R_267
