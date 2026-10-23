/-
# Round 710: the refined certificate at `L = 2249/1000` with `n = 300`, parts 316–318 of 503

File 83 of 127: the parts `rows2249R_316` … `rows2249R_318` of `SieveCert2249R.lean`'s certificate on
`SieveGrid2249R.grid2249R` (3 parts, 22463 tests: row 105 columns 0–51, row 105 columns 52–58, row 105 columns
59–65), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows2249R_316 : rowsJ2 105 106 0 52 ≤ 362539571678264 := by decide +kernel

theorem rows2249R_317 : rowsJ2 105 106 52 59 ≤ 16712358676499 := by decide +kernel

theorem rows2249R_318 : rowsJ2 105 106 59 66 ≤ 499250743946 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2249R_316
#print axioms SieveCert.rows2249R_318
