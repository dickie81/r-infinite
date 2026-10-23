/-
# Round 705: the refined certificate at `L = 9/4` with `n = 200`, parts 21–24 of 117

File 6 of 27: the parts `rows225R_21` … `rows225R_24` of `SieveCert225R.lean`'s certificate on
`SieveGrid225R.grid225R` (4 parts, 22782 tests: rows 44–44, rows 45–45, row 46 columns 0–45, row 46 columns 46–199),
each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
false`).

The file imports `SieveGrid225R.lean`.
-/
import SieveGrid225R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid225R

theorem rows225R_21 : rows2 44 45 ≤ 2980120255979537 := by decide +kernel

theorem rows225R_22 : rows2 45 46 ≤ 2845460501598157 := by decide +kernel

theorem rows225R_23 : rowsJ2 46 47 0 46 ≤ 2694324915768072 := by decide +kernel

theorem rows225R_24 : rowsJ2 46 47 46 200 ≤ 16527421450180 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225R_21
#print axioms SieveCert.rows225R_24
