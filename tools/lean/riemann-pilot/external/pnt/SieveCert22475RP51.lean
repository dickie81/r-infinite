/-
# Round 710: the refined certificate at `L = 899/400` with `n = 300`, parts 199–201 of 534

File 51 of 135: the parts `rows22475R_199` … `rows22475R_201` of `SieveCert22475R.lean`'s certificate on
`SieveGrid22475R.grid22475R` (3 parts, 22970 tests: row 83 columns 68–72, row 83 columns 73–77, row 83 columns
78–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows22475R_199 : rowsJ2 83 84 68 73 ≤ 6217696642204 := by decide +kernel

theorem rows22475R_200 : rowsJ2 83 84 73 78 ≤ 3213279231366 := by decide +kernel

theorem rows22475R_201 : rowsJ2 83 84 78 300 ≤ 11212163511847 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22475R_199
#print axioms SieveCert.rows22475R_201
