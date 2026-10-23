/-
# Round 710: the refined certificate at `L = 899/400` with `n = 300`, parts 107–110 of 534

File 27 of 135: the parts `rows22475R_107` … `rows22475R_110` of `SieveCert22475R.lean`'s certificate on
`SieveGrid22475R.grid22475R` (4 parts, 24442 tests: row 65 columns 0–34, row 65 columns 35–44, row 65 columns 45–62,
row 65 columns 63–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`,
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

theorem rows22475R_107 : rowsJ2 65 66 0 35 ≤ 828295200254765 := by decide +kernel

theorem rows22475R_108 : rowsJ2 65 66 35 45 ≤ 545566574471689 := by decide +kernel

theorem rows22475R_109 : rowsJ2 65 66 45 63 ≤ 801542278826479 := by decide +kernel

theorem rows22475R_110 : rowsJ2 65 66 63 300 ≤ 73166303549289 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22475R_107
#print axioms SieveCert.rows22475R_110
