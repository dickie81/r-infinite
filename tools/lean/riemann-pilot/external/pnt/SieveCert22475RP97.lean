/-
# Round 710: the refined certificate at `L = 899/400` with `n = 300`, parts 374–376 of 534

File 97 of 135: the parts `rows22475R_374` … `rows22475R_376` of `SieveCert22475R.lean`'s certificate on
`SieveGrid22475R.grid22475R` (3 parts, 23178 tests: row 113 columns 0–50, row 113 columns 51–57, row 113 columns
58–65), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows22475R_374 : rowsJ2 113 114 0 51 ≤ 306335583139699 := by decide +kernel

theorem rows22475R_375 : rowsJ2 113 114 51 58 ≤ 45398513453936 := by decide +kernel

theorem rows22475R_376 : rowsJ2 113 114 58 66 ≤ 15361017118170 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22475R_374
#print axioms SieveCert.rows22475R_376
