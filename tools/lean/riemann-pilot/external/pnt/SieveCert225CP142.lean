/-
# Round 625: the certificate at `L = 9/4`, parts 1156–1163 of 1374

File 142 of 167: the parts `rows225C_1156` … `rows225C_1163` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (8 parts, 55511 depth-4 tests: row 165 columns 0–54, row 165 columns 55–60, row 165 columns
61–64, row 165 columns 65–69, row 165 columns 70–75, row 165 columns 76–83, row 165 columns 84–399, row 166 columns
0–54), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
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

theorem rows225C_1156 : rowsJ 165 166 0 55 ≤ 58140560605152 := by decide +kernel

theorem rows225C_1157 : rowsJ 165 166 55 61 ≤ 23605820448947 := by decide +kernel

theorem rows225C_1158 : rowsJ 165 166 61 65 ≤ 20613982654464 := by decide +kernel

theorem rows225C_1159 : rowsJ 165 166 65 70 ≤ 15035119455607 := by decide +kernel

theorem rows225C_1160 : rowsJ 165 166 70 76 ≤ 6753650347794 := by decide +kernel

theorem rows225C_1161 : rowsJ 165 166 76 84 ≤ 816040793268 := by decide +kernel

theorem rows225C_1162 : rowsJ 165 166 84 400 ≤ 747328257679016 := by decide +kernel

theorem rows225C_1163 : rowsJ 166 167 0 55 ≤ 55444298279327 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_1156
#print axioms SieveCert.rows225C_1163
