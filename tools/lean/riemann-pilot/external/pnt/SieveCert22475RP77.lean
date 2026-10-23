/-
# Round 710: the refined certificate at `L = 899/400` with `n = 300`, parts 300–303 of 534

File 77 of 135: the parts `rows22475R_300` … `rows22475R_303` of `SieveCert22475R.lean`'s certificate on
`SieveGrid22475R.grid22475R` (4 parts, 25694 tests: row 98 columns 72–79, row 98 columns 80–299, row 99 columns
0–52, row 99 columns 53–59), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22475R_300 : rowsJ2 98 99 72 80 ≤ 24308210414340 := by decide +kernel

theorem rows22475R_301 : rowsJ2 98 99 80 300 ≤ 1575390224547669 := by decide +kernel

theorem rows22475R_302 : rowsJ2 99 100 0 53 ≤ 561235670443561 := by decide +kernel

theorem rows22475R_303 : rowsJ2 99 100 53 60 ≤ 975329317275 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22475R_300
#print axioms SieveCert.rows22475R_303
