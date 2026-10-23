/-
# Round 710: the refined certificate at `L = 899/400` with `n = 300`, parts 24–27 of 534

File 6 of 135: the parts `rows22475R_24` … `rows22475R_27` of `SieveCert22475R.lean`'s certificate on
`SieveGrid22475R.grid22475R` (4 parts, 27434 tests: row 41 columns 0–34, row 41 columns 35–299, row 42 columns 0–34,
row 42 columns 35–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`,
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

theorem rows22475R_24 : rowsJ2 41 42 0 35 ≤ 2486922275757623 := by decide +kernel

theorem rows22475R_25 : rowsJ2 41 42 35 300 ≤ 423321207458707 := by decide +kernel

theorem rows22475R_26 : rowsJ2 42 43 0 35 ≤ 2407789876492672 := by decide +kernel

theorem rows22475R_27 : rowsJ2 42 43 35 300 ≤ 451581072012636 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22475R_24
#print axioms SieveCert.rows22475R_27
