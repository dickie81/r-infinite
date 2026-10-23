/-
# Round 710: the refined certificate at `L = 899/400` with `n = 300`, parts 63–66 of 534

File 16 of 135: the parts `rows22475R_63` … `rows22475R_66` of `SieveCert22475R.lean`'s certificate on
`SieveGrid22475R.grid22475R` (4 parts, 25840 tests: row 54 columns 0–34, row 54 columns 35–43, row 54 columns 44–50,
row 54 columns 51–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`,
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

theorem rows22475R_63 : rowsJ2 54 55 0 35 ≤ 1492766054109193 := by decide +kernel

theorem rows22475R_64 : rowsJ2 54 55 35 44 ≤ 349470706568019 := by decide +kernel

theorem rows22475R_65 : rowsJ2 54 55 44 51 ≤ 504139794397635 := by decide +kernel

theorem rows22475R_66 : rowsJ2 54 55 51 300 ≤ 265337817656758 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22475R_63
#print axioms SieveCert.rows22475R_66
