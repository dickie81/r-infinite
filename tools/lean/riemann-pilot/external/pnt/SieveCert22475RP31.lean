/-
# Round 710: the refined certificate at `L = 899/400` with `n = 300`, parts 123–126 of 534

File 31 of 135: the parts `rows22475R_123` … `rows22475R_126` of `SieveCert22475R.lean`'s certificate on
`SieveGrid22475R.grid22475R` (4 parts, 26222 tests: row 69 columns 0–34, row 69 columns 35–45, row 69 columns 46–66,
row 69 columns 67–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`,
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

theorem rows22475R_123 : rowsJ2 69 70 0 35 ≤ 670366764967756 := by decide +kernel

theorem rows22475R_124 : rowsJ2 69 70 35 46 ≤ 622238899613097 := by decide +kernel

theorem rows22475R_125 : rowsJ2 69 70 46 67 ≤ 678839379221902 := by decide +kernel

theorem rows22475R_126 : rowsJ2 69 70 67 300 ≤ 37106993616259 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22475R_123
#print axioms SieveCert.rows22475R_126
