/-
# Round 705: the refined certificate at `L = 9/4` with `n = 200`, parts 67–71 of 117

File 17 of 27: the parts `rows225R_67` … `rows225R_71` of `SieveCert225R.lean`'s certificate on
`SieveGrid225R.grid225R` (5 parts, 29769 tests: row 68 columns 0–44, row 68 columns 45–199, row 69 columns 0–44, row
69 columns 45–199, row 70 columns 0–44), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
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

theorem rows225R_67 : rowsJ2 68 69 0 45 ≤ 720623685472730 := by decide +kernel

theorem rows225R_68 : rowsJ2 68 69 45 200 ≤ 1593329786515125 := by decide +kernel

theorem rows225R_69 : rowsJ2 69 70 0 45 ≤ 685218995860874 := by decide +kernel

theorem rows225R_70 : rowsJ2 69 70 45 200 ≤ 1324225585700887 := by decide +kernel

theorem rows225R_71 : rowsJ2 70 71 0 45 ≤ 662608349889720 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225R_67
#print axioms SieveCert.rows225R_71
