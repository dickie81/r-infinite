/-
# Round 710: the refined certificate at `L = 2249/1000` with `n = 300`, parts 104–106 of 503

File 27 of 127: the parts `rows2249R_104` … `rows2249R_106` of `SieveCert2249R.lean`'s certificate on
`SieveGrid2249R.grid2249R` (3 parts, 22693 tests: row 65 columns 0–34, row 65 columns 35–45, row 65 columns 46–299),
each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
false`).

The file imports `SieveGrid2249R.lean`.
-/
import SieveGrid2249R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid2249R

theorem rows2249R_104 : rowsJ2 65 66 0 35 ≤ 670035552485468 := by decide +kernel

theorem rows2249R_105 : rowsJ2 65 66 35 46 ≤ 601328881898008 := by decide +kernel

theorem rows2249R_106 : rowsJ2 65 66 46 300 ≤ 675591583994262 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2249R_104
#print axioms SieveCert.rows2249R_106
