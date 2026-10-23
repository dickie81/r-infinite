/-
# Round 710: the refined certificate at `L = 899/400` with `n = 300`, parts 251–254 of 534

File 65 of 135: the parts `rows22475R_251` … `rows22475R_254` of `SieveCert22475R.lean`'s certificate on
`SieveGrid22475R.grid22475R` (4 parts, 29570 tests: row 91 columns 0–47, row 91 columns 48–61, row 91 columns 62–66,
row 91 columns 67–71), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one
at a time (`Elab.async false`).

The file imports `SieveGrid22475R.lean`.
-/
import SieveGrid22475R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22475R

theorem rows22475R_251 : rowsJ2 91 92 0 48 ≤ 755578892402683 := by decide +kernel

theorem rows22475R_252 : rowsJ2 91 92 48 62 ≤ 30768988714328 := by decide +kernel

theorem rows22475R_253 : rowsJ2 91 92 62 67 ≤ 177894804414 := by decide +kernel

theorem rows22475R_254 : rowsJ2 91 92 67 72 ≤ 22578896213 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22475R_251
#print axioms SieveCert.rows22475R_254
