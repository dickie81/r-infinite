/-
# Round 625: the certificate at `L = 9/4`, parts 1237–1244 of 1374

File 152 of 167: the parts `rows225C_1237` … `rows225C_1244` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (8 parts, 53314 depth-4 tests: row 178 columns 63–70, row 178 columns 71–399, row 179
columns 0–49, row 179 columns 50–55, row 179 columns 56–61, row 179 columns 62–69, row 179 columns 70–399, row 180
columns 0–49), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows225C_1237 : rowsJ 178 179 63 71 ≤ 9881484993122 := by decide +kernel

theorem rows225C_1238 : rowsJ 178 179 71 400 ≤ 1825510031551490 := by decide +kernel

theorem rows225C_1239 : rowsJ 179 180 0 50 ≤ 29771845496463 := by decide +kernel

theorem rows225C_1240 : rowsJ 179 180 50 56 ≤ 34961917317646 := by decide +kernel

theorem rows225C_1241 : rowsJ 179 180 56 62 ≤ 27055081295341 := by decide +kernel

theorem rows225C_1242 : rowsJ 179 180 62 70 ≤ 11274329832055 := by decide +kernel

theorem rows225C_1243 : rowsJ 179 180 70 400 ≤ 1838408611183490 := by decide +kernel

theorem rows225C_1244 : rowsJ 180 181 0 50 ≤ 30612576178098 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_1237
#print axioms SieveCert.rows225C_1244
