/-
# Round 710: the refined certificate at `L = 899/400` with `n = 300`, parts 51–54 of 534

File 13 of 135: the parts `rows22475R_51` … `rows22475R_54` of `SieveCert22475R.lean`'s certificate on
`SieveGrid22475R.grid22475R` (4 parts, 24020 tests: row 51 columns 0–34, row 51 columns 35–43, row 51 columns 44–50,
row 51 columns 51–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`,
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

theorem rows22475R_51 : rowsJ2 51 52 0 35 ≤ 1711218096803497 := by decide +kernel

theorem rows22475R_52 : rowsJ2 51 52 35 44 ≤ 354072871649946 := by decide +kernel

theorem rows22475R_53 : rowsJ2 51 52 44 51 ≤ 502319701033194 := by decide +kernel

theorem rows22475R_54 : rowsJ2 51 52 51 300 ≤ 73859100504806 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22475R_51
#print axioms SieveCert.rows22475R_54
