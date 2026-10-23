/-
# Round 705: the refined certificate at `L = 9/4` with `n = 200`, parts 9–12 of 117

File 3 of 27: the parts `rows225R_9` … `rows225R_12` of `SieveCert225R.lean`'s certificate on
`SieveGrid225R.grid225R` (4 parts, 27792 tests: rows 32–32, rows 33–33, rows 34–34, rows 35–35), each a sum of
refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid225R.lean`.
-/
import SieveGrid225R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid225R

theorem rows225R_9 : rows2 32 33 ≤ 3510088736542179 := by decide +kernel

theorem rows225R_10 : rows2 33 34 ≤ 3531285323689409 := by decide +kernel

theorem rows225R_11 : rows2 34 35 ≤ 3550779614556701 := by decide +kernel

theorem rows225R_12 : rows2 35 36 ≤ 3552451765986294 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225R_9
#print axioms SieveCert.rows225R_12
