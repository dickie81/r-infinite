/-
# Round 625: the certificate at `L = 9/4`, parts 1042–1049 of 1374

File 128 of 167: the parts `rows225C_1042` … `rows225C_1049` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (8 parts, 59756 depth-4 tests: row 151 columns 0–59, row 151 columns 60–65, row 151 columns
66–69, row 151 columns 70–73, row 151 columns 74–77, row 151 columns 78–82, row 151 columns 83–88, row 151 columns
89–95), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
false`).

The file imports `SieveGrid225C.lean`.
-/
import SieveGrid225C

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid225C

theorem rows225C_1042 : rowsJ 151 152 0 60 ≤ 126060324836516 := by decide +kernel

theorem rows225C_1043 : rowsJ 151 152 60 66 ≤ 15226176894554 := by decide +kernel

theorem rows225C_1044 : rowsJ 151 152 66 70 ≤ 15405199169339 := by decide +kernel

theorem rows225C_1045 : rowsJ 151 152 70 74 ≤ 11815537414837 := by decide +kernel

theorem rows225C_1046 : rowsJ 151 152 74 78 ≤ 6783786769457 := by decide +kernel

theorem rows225C_1047 : rowsJ 151 152 78 83 ≤ 3616239101555 := by decide +kernel

theorem rows225C_1048 : rowsJ 151 152 83 89 ≤ 650968816070 := by decide +kernel

theorem rows225C_1049 : rowsJ 151 152 89 96 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_1042
#print axioms SieveCert.rows225C_1049
