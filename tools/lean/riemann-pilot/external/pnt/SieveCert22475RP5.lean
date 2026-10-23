/-
# Round 710: the refined certificate at `L = 899/400` with `n = 300`, parts 20–23 of 534

File 5 of 135: the parts `rows22475R_20` … `rows22475R_23` of `SieveCert22475R.lean`'s certificate on
`SieveGrid22475R.grid22475R` (4 parts, 23821 tests: row 39 columns 0–34, row 39 columns 35–299, row 40 columns 0–34,
row 40 columns 35–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`,
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

theorem rows22475R_20 : rowsJ2 39 40 0 35 ≤ 2644899819622365 := by decide +kernel

theorem rows22475R_21 : rowsJ2 39 40 35 300 ≤ 356410623465835 := by decide +kernel

theorem rows22475R_22 : rowsJ2 40 41 0 35 ≤ 2565788733195919 := by decide +kernel

theorem rows22475R_23 : rowsJ2 40 41 35 300 ≤ 392596023972140 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22475R_20
#print axioms SieveCert.rows22475R_23
