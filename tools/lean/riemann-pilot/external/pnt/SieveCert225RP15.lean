/-
# Round 705: the refined certificate at `L = 9/4` with `n = 200`, parts 59–62 of 117

File 15 of 27: the parts `rows225R_59` … `rows225R_62` of `SieveCert225R.lean`'s certificate on
`SieveGrid225R.grid225R` (4 parts, 24800 tests: row 64 columns 0–44, row 64 columns 45–199, row 65 columns 0–44, row
65 columns 45–199), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at
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

theorem rows225R_59 : rowsJ2 64 65 0 45 ≤ 893756735294141 := by decide +kernel

theorem rows225R_60 : rowsJ2 64 65 45 200 ≤ 2228354667869852 := by decide +kernel

theorem rows225R_61 : rowsJ2 65 66 0 45 ≤ 839600258200890 := by decide +kernel

theorem rows225R_62 : rowsJ2 65 66 45 200 ≤ 1938916055485588 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225R_59
#print axioms SieveCert.rows225R_62
