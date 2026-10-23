/-
# Round 710: the refined certificate at `L = 899/400` with `n = 300`, parts 380–383 of 534

File 99 of 135: the parts `rows22475R_380` … `rows22475R_383` of `SieveCert22475R.lean`'s certificate on
`SieveGrid22475R.grid22475R` (4 parts, 28753 tests: row 114 columns 58–65, row 114 columns 66–299, row 115 columns
0–49, row 115 columns 50–56), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
+kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22475R.lean`.
-/
import SieveGrid22475R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22475R

theorem rows22475R_380 : rowsJ2 114 115 58 66 ≤ 15059103523622 := by decide +kernel

theorem rows22475R_381 : rowsJ2 114 115 66 300 ≤ 558076417742154 := by decide +kernel

theorem rows22475R_382 : rowsJ2 115 116 0 50 ≤ 275345542651219 := by decide +kernel

theorem rows22475R_383 : rowsJ2 115 116 50 57 ≤ 51100765358841 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22475R_380
#print axioms SieveCert.rows22475R_383
