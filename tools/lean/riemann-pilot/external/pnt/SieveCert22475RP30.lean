/-
# Round 710: the refined certificate at `L = 899/400` with `n = 300`, parts 119–122 of 534

File 30 of 135: the parts `rows22475R_119` … `rows22475R_122` of `SieveCert22475R.lean`'s certificate on
`SieveGrid22475R.grid22475R` (4 parts, 25420 tests: row 68 columns 0–34, row 68 columns 35–45, row 68 columns 46–65,
row 68 columns 66–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`,
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

theorem rows22475R_119 : rowsJ2 68 69 0 35 ≤ 704383155025034 := by decide +kernel

theorem rows22475R_120 : rowsJ2 68 69 35 46 ≤ 622685655560418 := by decide +kernel

theorem rows22475R_121 : rowsJ2 68 69 46 66 ≤ 701519778783147 := by decide +kernel

theorem rows22475R_122 : rowsJ2 68 69 66 300 ≤ 44912074906180 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22475R_119
#print axioms SieveCert.rows22475R_122
