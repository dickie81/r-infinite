/-
# Round 710: the refined certificate at `L = 899/400` with `n = 300`, parts 209–211 of 534

File 54 of 135: the parts `rows22475R_209` … `rows22475R_211` of `SieveCert22475R.lean`'s certificate on
`SieveGrid22475R.grid22475R` (3 parts, 23062 tests: row 85 columns 0–36, row 85 columns 37–61, row 85 columns
62–67), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows22475R_209 : rowsJ2 85 86 0 37 ≤ 587635228225545 := by decide +kernel

theorem rows22475R_210 : rowsJ2 85 86 37 62 ≤ 433522938125689 := by decide +kernel

theorem rows22475R_211 : rowsJ2 85 86 62 68 ≤ 1530116667954 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22475R_209
#print axioms SieveCert.rows22475R_211
