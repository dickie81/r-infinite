/-
# Round 710: the refined certificate at `L = 899/400` with `n = 300`, parts 168–171 of 534

File 43 of 135: the parts `rows22475R_168` … `rows22475R_171` of `SieveCert22475R.lean`'s certificate on
`SieveGrid22475R.grid22475R` (4 parts, 25181 tests: row 78 columns 68–72, row 78 columns 73–76, row 78 columns
77–299, row 79 columns 0–34), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22475R_168 : rowsJ2 78 79 68 73 ≤ 12802147330113 := by decide +kernel

theorem rows22475R_169 : rowsJ2 78 79 73 77 ≤ 10320150799894 := by decide +kernel

theorem rows22475R_170 : rowsJ2 78 79 77 300 ≤ 3865284451388 := by decide +kernel

theorem rows22475R_171 : rowsJ2 79 80 0 35 ≤ 515165677777824 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22475R_168
#print axioms SieveCert.rows22475R_171
