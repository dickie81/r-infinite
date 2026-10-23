/-
# Round 710: the refined certificate at `L = 899/400` with `n = 300`, parts 146–149 of 534

File 37 of 135: the parts `rows22475R_146` … `rows22475R_149` of `SieveCert22475R.lean`'s certificate on
`SieveGrid22475R.grid22475R` (4 parts, 25829 tests: row 74 columns 51–67, row 74 columns 68–72, row 74 columns
73–299, row 75 columns 0–34), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22475R_146 : rowsJ2 74 75 51 68 ≤ 305154295582491 := by decide +kernel

theorem rows22475R_147 : rowsJ2 74 75 68 73 ≤ 24470731191606 := by decide +kernel

theorem rows22475R_148 : rowsJ2 74 75 73 300 ≤ 10707046342486 := by decide +kernel

theorem rows22475R_149 : rowsJ2 75 76 0 35 ≤ 539909611831770 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22475R_146
#print axioms SieveCert.rows22475R_149
