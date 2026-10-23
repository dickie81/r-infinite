/-
# Round 710: the refined certificate at `L = 899/400` with `n = 300`, parts 243–246 of 534

File 63 of 135: the parts `rows22475R_243` … `rows22475R_246` of `SieveCert22475R.lean`'s certificate on
`SieveGrid22475R.grid22475R` (4 parts, 25339 tests: row 89 columns 85–299, row 90 columns 0–42, row 90 columns
43–61, row 90 columns 62–66), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22475R_243 : rowsJ2 89 90 85 300 ≤ 354777323313413 := by decide +kernel

theorem rows22475R_244 : rowsJ2 90 91 0 43 ≤ 708990635962525 := by decide +kernel

theorem rows22475R_245 : rowsJ2 90 91 43 62 ≤ 113394939450808 := by decide +kernel

theorem rows22475R_246 : rowsJ2 90 91 62 67 ≤ 377328071656 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22475R_243
#print axioms SieveCert.rows22475R_246
