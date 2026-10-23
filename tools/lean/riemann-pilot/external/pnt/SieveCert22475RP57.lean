/-
# Round 710: the refined certificate at `L = 899/400` with `n = 300`, parts 220–223 of 534

File 57 of 135: the parts `rows22475R_220` … `rows22475R_223` of `SieveCert22475R.lean`'s certificate on
`SieveGrid22475R.grid22475R` (4 parts, 26571 tests: row 86 columns 72–76, row 86 columns 77–82, row 86 columns
83–299, row 87 columns 0–37), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
+kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22475R.lean`.
-/
import SieveGrid22475R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22475R

theorem rows22475R_220 : rowsJ2 86 87 72 77 ≤ 1104401177392 := by decide +kernel

theorem rows22475R_221 : rowsJ2 86 87 77 83 ≤ 12663564601566 := by decide +kernel

theorem rows22475R_222 : rowsJ2 86 87 83 300 ≤ 27526728016618 := by decide +kernel

theorem rows22475R_223 : rowsJ2 87 88 0 38 ≤ 612249130866674 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22475R_220
#print axioms SieveCert.rows22475R_223
