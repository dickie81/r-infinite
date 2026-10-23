/-
# Round 710: the refined certificate at `L = 2249/1000` with `n = 300`, parts 14–19 of 503

File 4 of 127: the parts `rows2249R_14` … `rows2249R_19` of `SieveCert2249R.lean`'s certificate on
`SieveGrid2249R.grid2249R` (6 parts, 29679 tests: row 36 columns 0–34, row 36 columns 35–299, row 37 columns 0–34,
row 37 columns 35–299, row 38 columns 0–34, row 38 columns 35–299), each a sum of refined costs (`rows2` or
`rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid2249R.lean`.
-/
import SieveGrid2249R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid2249R

theorem rows2249R_14 : rowsJ2 36 37 0 35 ≤ 2536316698036433 := by decide +kernel

theorem rows2249R_15 : rowsJ2 36 37 35 300 ≤ 148094806255400 := by decide +kernel

theorem rows2249R_16 : rowsJ2 37 38 0 35 ≤ 2459444276716986 := by decide +kernel

theorem rows2249R_17 : rowsJ2 37 38 35 300 ≤ 201453815503930 := by decide +kernel

theorem rows2249R_18 : rowsJ2 38 39 0 35 ≤ 2382878510260237 := by decide +kernel

theorem rows2249R_19 : rowsJ2 38 39 35 300 ≤ 244427440615279 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2249R_14
#print axioms SieveCert.rows2249R_19
