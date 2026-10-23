/-
# Round 705: the refined certificate at `L = 9/4` with `n = 200`, parts 51–54 of 117

File 13 of 27: the parts `rows225R_51` … `rows225R_54` of `SieveCert225R.lean`'s certificate on
`SieveGrid225R.grid225R` (4 parts, 27320 tests: row 60 columns 0–44, row 60 columns 45–199, row 61 columns 0–44, row
61 columns 45–199), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at
a time (`Elab.async false`).

The file imports `SieveGrid225R.lean`.
-/
import SieveGrid225R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid225R

theorem rows225R_51 : rowsJ2 60 61 0 45 ≤ 1138256858100352 := by decide +kernel

theorem rows225R_52 : rowsJ2 60 61 45 200 ≤ 1389300371340213 := by decide +kernel

theorem rows225R_53 : rowsJ2 61 62 0 45 ≤ 1066333317006052 := by decide +kernel

theorem rows225R_54 : rowsJ2 61 62 45 200 ≤ 1648189221222477 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225R_51
#print axioms SieveCert.rows225R_54
