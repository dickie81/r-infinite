/-
# Round 710: the refined certificate at `L = 899/400` with `n = 300`, parts 288–291 of 534

File 74 of 135: the parts `rows22475R_288` … `rows22475R_291` of `SieveCert22475R.lean`'s certificate on
`SieveGrid22475R.grid22475R` (4 parts, 27960 tests: row 96 columns 72–78, row 96 columns 79–299, row 97 columns
0–52, row 97 columns 53–60), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22475R_288 : rowsJ2 96 97 72 79 ≤ 14464952910974 := by decide +kernel

theorem rows22475R_289 : rowsJ2 96 97 79 300 ≤ 1666729649250850 := by decide +kernel

theorem rows22475R_290 : rowsJ2 97 98 0 53 ≤ 609128377889811 := by decide +kernel

theorem rows22475R_291 : rowsJ2 97 98 53 61 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22475R_288
#print axioms SieveCert.rows22475R_291
