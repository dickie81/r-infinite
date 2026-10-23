/-
# Round 710: the refined certificate at `L = 899/400` with `n = 300`, parts 232–234 of 534

File 60 of 135: the parts `rows22475R_232` … `rows22475R_234` of `SieveCert22475R.lean`'s certificate on
`SieveGrid22475R.grid22475R` (3 parts, 22170 tests: row 88 columns 62–66, row 88 columns 67–71, row 88 columns
72–77), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
(`Elab.async false`).

The file imports `SieveGrid22475R.lean`.
-/
import SieveGrid22475R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22475R

theorem rows22475R_232 : rowsJ2 88 89 62 67 ≤ 692545520134 := by decide +kernel

theorem rows22475R_233 : rowsJ2 88 89 67 72 ≤ 1074566904518 := by decide +kernel

theorem rows22475R_234 : rowsJ2 88 89 72 78 ≤ 2053687329334 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22475R_232
#print axioms SieveCert.rows22475R_234
