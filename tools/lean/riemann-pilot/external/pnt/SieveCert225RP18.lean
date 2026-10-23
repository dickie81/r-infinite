/-
# Round 705: the refined certificate at `L = 9/4` with `n = 200`, parts 72–76 of 117

File 18 of 27: the parts `rows225R_72` … `rows225R_76` of `SieveCert225R.lean`'s certificate on
`SieveGrid225R.grid225R` (5 parts, 22848 tests: row 70 columns 45–199, row 71 columns 0–44, row 71 columns 45–199,
row 72 columns 0–44, row 72 columns 45–199), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
`decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid225R.lean`.
-/
import SieveGrid225R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid225R

theorem rows225R_72 : rowsJ2 70 71 45 200 ≤ 1298916016703162 := by decide +kernel

theorem rows225R_73 : rowsJ2 71 72 0 45 ≤ 633625585561271 := by decide +kernel

theorem rows225R_74 : rowsJ2 71 72 45 200 ≤ 1042143204071918 := by decide +kernel

theorem rows225R_75 : rowsJ2 72 73 0 45 ≤ 615677157578453 := by decide +kernel

theorem rows225R_76 : rowsJ2 72 73 45 200 ≤ 1029566397214787 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225R_72
#print axioms SieveCert.rows225R_76
