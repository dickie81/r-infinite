/-
# Round 710: the refined certificate at `L = 899/400` with `n = 300`, parts 228–231 of 534

File 59 of 135: the parts `rows22475R_228` … `rows22475R_231` of `SieveCert22475R.lean`'s certificate on
`SieveGrid22475R.grid22475R` (4 parts, 27605 tests: row 87 columns 77–82, row 87 columns 83–299, row 88 columns
0–38, row 88 columns 39–61), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22475R_228 : rowsJ2 87 88 77 83 ≤ 14698812075760 := by decide +kernel

theorem rows22475R_229 : rowsJ2 87 88 83 300 ≤ 41178844409018 := by decide +kernel

theorem rows22475R_230 : rowsJ2 88 89 0 39 ≤ 637141102783558 := by decide +kernel

theorem rows22475R_231 : rowsJ2 88 89 39 62 ≤ 259721887641534 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22475R_228
#print axioms SieveCert.rows22475R_231
