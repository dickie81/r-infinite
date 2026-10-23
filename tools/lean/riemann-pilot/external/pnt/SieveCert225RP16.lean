/-
# Round 705: the refined certificate at `L = 9/4` with `n = 200`, parts 63–66 of 117

File 16 of 27: the parts `rows225R_63` … `rows225R_66` of `SieveCert225R.lean`'s certificate on
`SieveGrid225R.grid225R` (4 parts, 23389 tests: row 66 columns 0–44, row 66 columns 45–199, row 67 columns 0–44, row
67 columns 45–199), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at
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

theorem rows225R_63 : rowsJ2 66 67 0 45 ≤ 797520230262628 := by decide +kernel

theorem rows225R_64 : rowsJ2 66 67 45 200 ≤ 1904094277813365 := by decide +kernel

theorem rows225R_65 : rowsJ2 67 68 0 45 ≤ 752572922937709 := by decide +kernel

theorem rows225R_66 : rowsJ2 67 68 45 200 ≤ 1624997941772124 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225R_63
#print axioms SieveCert.rows225R_66
