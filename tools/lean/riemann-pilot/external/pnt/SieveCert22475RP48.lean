/-
# Round 710: the refined certificate at `L = 899/400` with `n = 300`, parts 187–190 of 534

File 48 of 135: the parts `rows22475R_187` … `rows22475R_190` of `SieveCert22475R.lean`'s certificate on
`SieveGrid22475R.grid22475R` (4 parts, 29540 tests: row 81 columns 72–76, row 81 columns 77–299, row 82 columns
0–34, row 82 columns 35–60), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22475R_187 : rowsJ2 81 82 72 77 ≤ 6856860830895 := by decide +kernel

theorem rows22475R_188 : rowsJ2 81 82 77 300 ≤ 5596420796265 := by decide +kernel

theorem rows22475R_189 : rowsJ2 82 83 0 35 ≤ 507977607100741 := by decide +kernel

theorem rows22475R_190 : rowsJ2 82 83 35 61 ≤ 651317718504803 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22475R_187
#print axioms SieveCert.rows22475R_190
