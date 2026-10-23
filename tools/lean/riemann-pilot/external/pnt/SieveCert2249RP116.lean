/-
# Round 710: the refined certificate at `L = 2249/1000` with `n = 300`, parts 446–450 of 503

File 116 of 127: the parts `rows2249R_446` … `rows2249R_450` of `SieveCert2249R.lean`'s certificate on
`SieveGrid2249R.grid2249R` (5 parts, 29517 tests: row 144 columns 0–41, row 144 columns 42–299, row 145 columns
0–40, row 145 columns 41–299, row 146 columns 0–40), each a sum of refined costs (`rows2` or `rowsJ2`) at most its
bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid2249R.lean`.
-/
import SieveGrid2249R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid2249R

theorem rows2249R_446 : rowsJ2 144 145 0 42 ≤ 145670806469069 := by decide +kernel

theorem rows2249R_447 : rowsJ2 144 145 42 300 ≤ 2386005741790975 := by decide +kernel

theorem rows2249R_448 : rowsJ2 145 146 0 41 ≤ 145741304036902 := by decide +kernel

theorem rows2249R_449 : rowsJ2 145 146 41 300 ≤ 2392886268786328 := by decide +kernel

theorem rows2249R_450 : rowsJ2 146 147 0 41 ≤ 151717315904917 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2249R_446
#print axioms SieveCert.rows2249R_450
