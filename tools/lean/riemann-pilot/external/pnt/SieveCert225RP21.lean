/-
# Round 705: the refined certificate at `L = 9/4` with `n = 200`, parts 89–92 of 117

File 21 of 27: the parts `rows225R_89` … `rows225R_92` of `SieveCert225R.lean`'s certificate on
`SieveGrid225R.grid225R` (4 parts, 29592 tests: rows 79–79, rows 80–80, rows 81–81, rows 82–82), each a sum of
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

theorem rows225R_89 : rows2 79 80 ≤ 679955062964441 := by decide +kernel

theorem rows225R_90 : rows2 80 81 ≤ 1091181411254322 := by decide +kernel

theorem rows225R_91 : rows2 81 82 ≤ 1484865915734994 := by decide +kernel

theorem rows225R_92 : rows2 82 83 ≤ 1878665699207759 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225R_89
#print axioms SieveCert.rows225R_92
