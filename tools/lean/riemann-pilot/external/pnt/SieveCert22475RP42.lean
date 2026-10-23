/-
# Round 710: the refined certificate at `L = 899/400` with `n = 300`, parts 165–167 of 534

File 42 of 135: the parts `rows22475R_165` … `rows22475R_167` of `SieveCert22475R.lean`'s certificate on
`SieveGrid22475R.grid22475R` (3 parts, 22499 tests: row 78 columns 0–34, row 78 columns 35–59, row 78 columns
60–67), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows22475R_165 : rowsJ2 78 79 0 35 ≤ 520127042851522 := by decide +kernel

theorem rows22475R_166 : rowsJ2 78 79 35 60 ≤ 827374189912317 := by decide +kernel

theorem rows22475R_167 : rowsJ2 78 79 60 68 ≤ 40660605789977 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22475R_165
#print axioms SieveCert.rows22475R_167
