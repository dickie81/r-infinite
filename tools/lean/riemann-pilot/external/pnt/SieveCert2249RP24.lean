/-
# Round 710: the refined certificate at `L = 2249/1000` with `n = 300`, parts 95–97 of 503

File 24 of 127: the parts `rows2249R_95` … `rows2249R_97` of `SieveCert2249R.lean`'s certificate on
`SieveGrid2249R.grid2249R` (3 parts, 23352 tests: row 62 columns 0–34, row 62 columns 35–44, row 62 columns 45–299),
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

theorem rows2249R_95 : rowsJ2 62 63 0 35 ≤ 787797298654806 := by decide +kernel

theorem rows2249R_96 : rowsJ2 62 63 35 45 ≤ 527605721323255 := by decide +kernel

theorem rows2249R_97 : rowsJ2 62 63 45 300 ≤ 773108190446228 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2249R_95
#print axioms SieveCert.rows2249R_97
