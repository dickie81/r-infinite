/-
# Round 710: the refined certificate at `L = 899/400` with `n = 300`, parts 91–94 of 534

File 23 of 135: the parts `rows22475R_91` … `rows22475R_94` of `SieveCert22475R.lean`'s certificate on
`SieveGrid22475R.grid22475R` (4 parts, 25780 tests: row 61 columns 0–34, row 61 columns 35–43, row 61 columns 44–54,
row 61 columns 55–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`,
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

theorem rows22475R_91 : rowsJ2 61 62 0 35 ≤ 1037825669468253 := by decide +kernel

theorem rows22475R_92 : rowsJ2 61 62 35 44 ≤ 427514142664109 := by decide +kernel

theorem rows22475R_93 : rowsJ2 61 62 44 55 ≤ 664728838141084 := by decide +kernel

theorem rows22475R_94 : rowsJ2 61 62 55 300 ≤ 304593803722526 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22475R_91
#print axioms SieveCert.rows22475R_94
