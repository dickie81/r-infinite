/-
# Round 710: the refined certificate at `L = 899/400` with `n = 300`, parts 255–258 of 534

File 66 of 135: the parts `rows22475R_255` … `rows22475R_258` of `SieveCert22475R.lean`'s certificate on
`SieveGrid22475R.grid22475R` (4 parts, 24510 tests: row 91 columns 72–77, row 91 columns 78–84, row 91 columns
85–299, row 92 columns 0–50), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22475R_255 : rowsJ2 91 92 72 78 ≤ 4406212592431 := by decide +kernel

theorem rows22475R_256 : rowsJ2 91 92 78 85 ≤ 39576682704497 := by decide +kernel

theorem rows22475R_257 : rowsJ2 91 92 85 300 ≤ 735215650563002 := by decide +kernel

theorem rows22475R_258 : rowsJ2 92 93 0 51 ≤ 748159684146103 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22475R_255
#print axioms SieveCert.rows22475R_258
