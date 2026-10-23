/-
# Round 710: the refined certificate at `L = 899/400` with `n = 300`, parts 481–485 of 534

File 124 of 135: the parts `rows22475R_481` … `rows22475R_485` of `SieveCert22475R.lean`'s certificate on
`SieveGrid22475R.grid22475R` (5 parts, 28970 tests: row 148 columns 0–40, row 148 columns 41–299, row 149 columns
0–40, row 149 columns 41–299, row 150 columns 0–40), each a sum of refined costs (`rows2` or `rowsJ2`) at most its
bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22475R.lean`.
-/
import SieveGrid22475R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22475R

theorem rows22475R_481 : rowsJ2 148 149 0 41 ≤ 167852986797355 := by decide +kernel

theorem rows22475R_482 : rowsJ2 148 149 41 300 ≤ 2536928627551909 := by decide +kernel

theorem rows22475R_483 : rowsJ2 149 150 0 41 ≤ 175427442835081 := by decide +kernel

theorem rows22475R_484 : rowsJ2 149 150 41 300 ≤ 2543490463856663 := by decide +kernel

theorem rows22475R_485 : rowsJ2 150 151 0 41 ≤ 183300105250051 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22475R_481
#print axioms SieveCert.rows22475R_485
