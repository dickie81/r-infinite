/-
# Round 710: the refined certificate at `L = 899/400` with `n = 300`, parts 259–262 of 534

File 67 of 135: the parts `rows22475R_259` … `rows22475R_262` of `SieveCert22475R.lean`'s certificate on
`SieveGrid22475R.grid22475R` (4 parts, 29004 tests: row 92 columns 51–61, row 92 columns 62–66, row 92 columns
67–71, row 92 columns 72–77), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22475R_259 : rowsJ2 92 93 51 62 ≤ 6140437042206 := by decide +kernel

theorem rows22475R_260 : rowsJ2 92 93 62 67 ≤ 66194484979 := by decide +kernel

theorem rows22475R_261 : rowsJ2 92 93 67 72 ≤ 0 := by decide +kernel

theorem rows22475R_262 : rowsJ2 92 93 72 78 ≤ 5545998387726 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22475R_259
#print axioms SieveCert.rows22475R_262
