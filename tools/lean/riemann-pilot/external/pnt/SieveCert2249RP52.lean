/-
# Round 710: the refined certificate at `L = 2249/1000` with `n = 300`, parts 197–200 of 503

File 52 of 127: the parts `rows2249R_197` … `rows2249R_200` of `SieveCert2249R.lean`'s certificate on
`SieveGrid2249R.grid2249R` (4 parts, 29587 tests: row 84 columns 79–299, row 85 columns 0–38, row 85 columns 39–62,
row 85 columns 63–67), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one
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

theorem rows2249R_197 : rowsJ2 84 85 79 300 ≤ 19430776752512 := by decide +kernel

theorem rows2249R_198 : rowsJ2 85 86 0 39 ≤ 609747524865547 := by decide +kernel

theorem rows2249R_199 : rowsJ2 85 86 39 63 ≤ 247851629526729 := by decide +kernel

theorem rows2249R_200 : rowsJ2 85 86 63 68 ≤ 1759564155790 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2249R_197
#print axioms SieveCert.rows2249R_200
