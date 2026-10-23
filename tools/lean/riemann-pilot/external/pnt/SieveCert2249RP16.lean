/-
# Round 710: the refined certificate at `L = 2249/1000` with `n = 300`, parts 63–66 of 503

File 16 of 127: the parts `rows2249R_63` … `rows2249R_66` of `SieveCert2249R.lean`'s certificate on
`SieveGrid2249R.grid2249R` (4 parts, 24660 tests: row 54 columns 0–34, row 54 columns 35–43, row 54 columns 44–51,
row 54 columns 52–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`,
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

theorem rows2249R_63 : rowsJ2 54 55 0 35 ≤ 1225768975834145 := by decide +kernel

theorem rows2249R_64 : rowsJ2 54 55 35 44 ≤ 357805900500417 := by decide +kernel

theorem rows2249R_65 : rowsJ2 54 55 44 52 ≤ 537575019674448 := by decide +kernel

theorem rows2249R_66 : rowsJ2 54 55 52 300 ≤ 175194098900565 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2249R_63
#print axioms SieveCert.rows2249R_66
