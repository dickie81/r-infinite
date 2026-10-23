/-
# Round 710: the refined certificate at `L = 2249/1000` with `n = 300`, parts 83–86 of 503

File 21 of 127: the parts `rows2249R_83` … `rows2249R_86` of `SieveCert2249R.lean`'s certificate on
`SieveGrid2249R.grid2249R` (4 parts, 24509 tests: row 59 columns 0–34, row 59 columns 35–43, row 59 columns 44–55,
row 59 columns 56–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`,
one at a time (`Elab.async false`).

The file imports `SieveGrid2249R.lean`.
-/
import SieveGrid2249R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid2249R

theorem rows2249R_83 : rowsJ2 59 60 0 35 ≤ 933534243711254 := by decide +kernel

theorem rows2249R_84 : rowsJ2 59 60 35 44 ≤ 429825967658491 := by decide +kernel

theorem rows2249R_85 : rowsJ2 59 60 44 56 ≤ 669909511647607 := by decide +kernel

theorem rows2249R_86 : rowsJ2 59 60 56 300 ≤ 164268281128899 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2249R_83
#print axioms SieveCert.rows2249R_86
