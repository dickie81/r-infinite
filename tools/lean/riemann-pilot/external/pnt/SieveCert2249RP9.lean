/-
# Round 710: the refined certificate at `L = 2249/1000` with `n = 300`, parts 36–39 of 503

File 9 of 127: the parts `rows2249R_36` … `rows2249R_39` of `SieveCert2249R.lean`'s certificate on
`SieveGrid2249R.grid2249R` (4 parts, 26194 tests: row 46 columns 0–34, row 46 columns 35–43, row 46 columns 44–299,
row 47 columns 0–34), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one
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

theorem rows2249R_36 : rowsJ2 46 47 0 35 ≤ 1778351983272975 := by decide +kernel

theorem rows2249R_37 : rowsJ2 46 47 35 44 ≤ 357595316527610 := by decide +kernel

theorem rows2249R_38 : rowsJ2 46 47 44 300 ≤ 179183612376247 := by decide +kernel

theorem rows2249R_39 : rowsJ2 47 48 0 35 ≤ 1705278401162958 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2249R_36
#print axioms SieveCert.rows2249R_39
