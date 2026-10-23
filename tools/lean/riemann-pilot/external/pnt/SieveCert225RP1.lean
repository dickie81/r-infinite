/-
# Round 705: the refined certificate at `L = 9/4` with `n = 200`, parts 0–3 of 117

File 1 of 27: the parts `rows225R_0` … `rows225R_3` of `SieveCert225R.lean`'s certificate on
`SieveGrid225R.grid225R` (4 parts, 27405 tests: rows 0–18, rows 19–22, rows 23–24, rows 25–26), each a sum of
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

theorem rows225R_0 : rows2 0 19 ≤ 23769383504989847 := by decide +kernel

theorem rows225R_1 : rows2 19 23 ≤ 15253967656262904 := by decide +kernel

theorem rows225R_2 : rows2 23 25 ≤ 7892773391935480 := by decide +kernel

theorem rows225R_3 : rows2 25 27 ≤ 7590997169677509 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225R_0
#print axioms SieveCert.rows225R_3
