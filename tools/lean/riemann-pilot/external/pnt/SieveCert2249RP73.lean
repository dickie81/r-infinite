/-
# Round 710: the refined certificate at `L = 2249/1000` with `n = 300`, parts 277–280 of 503

File 73 of 127: the parts `rows2249R_277` … `rows2249R_280` of `SieveCert2249R.lean`'s certificate on
`SieveGrid2249R.grid2249R` (4 parts, 24090 tests: row 97 columns 74–87, row 97 columns 88–299, row 98 columns 0–53,
row 98 columns 54–60), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one
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

theorem rows2249R_277 : rowsJ2 97 98 74 88 ≤ 661769257388885 := by decide +kernel

theorem rows2249R_278 : rowsJ2 97 98 88 300 ≤ 795752948251838 := by decide +kernel

theorem rows2249R_279 : rowsJ2 98 99 0 54 ≤ 489518020852783 := by decide +kernel

theorem rows2249R_280 : rowsJ2 98 99 54 61 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2249R_277
#print axioms SieveCert.rows2249R_280
