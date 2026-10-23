/-
# Round 710: the refined certificate at `L = 2249/1000` with `n = 300`, parts 331–333 of 503

File 87 of 127: the parts `rows2249R_331` … `rows2249R_333` of `SieveCert2249R.lean`'s certificate on
`SieveGrid2249R.grid2249R` (3 parts, 23349 tests: row 108 columns 0–51, row 108 columns 52–58, row 108 columns
59–66), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
(`Elab.async false`).

The file imports `SieveGrid2249R.lean`.
-/
import SieveGrid2249R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid2249R

theorem rows2249R_331 : rowsJ2 108 109 0 52 ≤ 317419076209654 := by decide +kernel

theorem rows2249R_332 : rowsJ2 108 109 52 59 ≤ 26486488393846 := by decide +kernel

theorem rows2249R_333 : rowsJ2 108 109 59 67 ≤ 3575790109248 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2249R_331
#print axioms SieveCert.rows2249R_333
