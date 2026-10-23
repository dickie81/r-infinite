/-
# Round 710: the refined certificate at `L = 899/400` with `n = 300`, parts 99–102 of 534

File 25 of 135: the parts `rows22475R_99` … `rows22475R_102` of `SieveCert22475R.lean`'s certificate on
`SieveGrid22475R.grid22475R` (4 parts, 24948 tests: row 63 columns 0–34, row 63 columns 35–43, row 63 columns 44–56,
row 63 columns 57–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`,
one at a time (`Elab.async false`).

The file imports `SieveGrid22475R.lean`.
-/
import SieveGrid22475R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22475R

theorem rows22475R_99 : rowsJ2 63 64 0 35 ≤ 927456605779242 := by decide +kernel

theorem rows22475R_100 : rowsJ2 63 64 35 44 ≤ 457180364556810 := by decide +kernel

theorem rows22475R_101 : rowsJ2 63 64 44 57 ≤ 715237824143799 := by decide +kernel

theorem rows22475R_102 : rowsJ2 63 64 57 300 ≤ 249576934102467 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22475R_99
#print axioms SieveCert.rows22475R_102
