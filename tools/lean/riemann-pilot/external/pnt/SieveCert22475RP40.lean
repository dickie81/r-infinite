/-
# Round 710: the refined certificate at `L = 899/400` with `n = 300`, parts 157–160 of 534

File 40 of 135: the parts `rows22475R_157` … `rows22475R_160` of `SieveCert22475R.lean`'s certificate on
`SieveGrid22475R.grid22475R` (4 parts, 29821 tests: row 76 columns 68–72, row 76 columns 73–299, row 77 columns
0–34, row 77 columns 35–58), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22475R_157 : rowsJ2 76 77 68 73 ≤ 16909983563199 := by decide +kernel

theorem rows22475R_158 : rowsJ2 76 77 73 300 ≤ 14811685106313 := by decide +kernel

theorem rows22475R_159 : rowsJ2 77 78 0 35 ≤ 523719154089697 := by decide +kernel

theorem rows22475R_160 : rowsJ2 77 78 35 59 ≤ 860666035300906 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22475R_157
#print axioms SieveCert.rows22475R_160
