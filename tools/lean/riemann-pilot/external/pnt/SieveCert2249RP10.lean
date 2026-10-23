/-
# Round 710: the refined certificate at `L = 2249/1000` with `n = 300`, parts 40–43 of 503

File 10 of 127: the parts `rows2249R_40` … `rows2249R_43` of `SieveCert2249R.lean`'s certificate on
`SieveGrid2249R.grid2249R` (4 parts, 27010 tests: row 47 columns 35–43, row 47 columns 44–299, row 48 columns 0–34,
row 48 columns 35–43), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one
at a time (`Elab.async false`).

The file imports `SieveGrid2249R.lean`.
-/
import SieveGrid2249R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid2249R

theorem rows2249R_40 : rowsJ2 47 48 35 44 ≤ 348855967460949 := by decide +kernel

theorem rows2249R_41 : rowsJ2 47 48 44 300 ≤ 256024290003444 := by decide +kernel

theorem rows2249R_42 : rowsJ2 48 49 0 35 ≤ 1633280144014760 := by decide +kernel

theorem rows2249R_43 : rowsJ2 48 49 35 44 ≤ 342300897616277 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2249R_40
#print axioms SieveCert.rows2249R_43
