/-
# Round 625: the certificate at `L = 9/4`, parts 645–652 of 1374

File 80 of 167: the parts `rows225C_645` … `rows225C_652` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (8 parts, 54411 depth-4 tests: row 117 columns 99–101, row 117 columns 102–105, row 117
columns 106–109, row 117 columns 110–114, row 117 columns 115–399, row 118 columns 0–34, row 118 columns 35–53, row
118 columns 54–75), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide +kernel`, one at a time
(`Elab.async false`).

The file imports `SieveGrid225C.lean`.
-/
import SieveGrid225C

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid225C

theorem rows225C_645 : rowsJ 117 118 99 102 ≤ 581014735328 := by decide +kernel

theorem rows225C_646 : rowsJ 117 118 102 106 ≤ 3236436465537 := by decide +kernel

theorem rows225C_647 : rowsJ 117 118 106 110 ≤ 8069540852948 := by decide +kernel

theorem rows225C_648 : rowsJ 117 118 110 115 ≤ 20540897911967 := by decide +kernel

theorem rows225C_649 : rowsJ 117 118 115 400 ≤ 114335186843578 := by decide +kernel

theorem rows225C_650 : rowsJ 118 119 0 35 ≤ 86636315011963 := by decide +kernel

theorem rows225C_651 : rowsJ 118 119 35 54 ≤ 294678676123923 := by decide +kernel

theorem rows225C_652 : rowsJ 118 119 54 76 ≤ 63162982415666 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_645
#print axioms SieveCert.rows225C_652
