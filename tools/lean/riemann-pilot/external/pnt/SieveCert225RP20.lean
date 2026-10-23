/-
# Round 705: the refined certificate at `L = 9/4` with `n = 200`, parts 83–88 of 117

File 20 of 27: the parts `rows225R_83` … `rows225R_88` of `SieveCert225R.lean`'s certificate on
`SieveGrid225R.grid225R` (6 parts, 25188 tests: row 76 columns 0–45, row 76 columns 46–199, row 77 columns 0–46, row
77 columns 47–199, row 78 columns 0–46, row 78 columns 47–199), each a sum of refined costs (`rows2` or `rowsJ2`) at
most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid225R.lean`.
-/
import SieveGrid225R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid225R

theorem rows225R_83 : rowsJ2 76 77 0 46 ≤ 528982642946366 := by decide +kernel

theorem rows225R_84 : rowsJ2 76 77 46 200 ≤ 510404017477813 := by decide +kernel

theorem rows225R_85 : rowsJ2 77 78 0 47 ≤ 500298640135416 := by decide +kernel

theorem rows225R_86 : rowsJ2 77 78 47 200 ≤ 262338606562731 := by decide +kernel

theorem rows225R_87 : rowsJ2 78 79 0 47 ≤ 481869256477113 := by decide +kernel

theorem rows225R_88 : rowsJ2 78 79 47 200 ≤ 253998121519977 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225R_83
#print axioms SieveCert.rows225R_88
