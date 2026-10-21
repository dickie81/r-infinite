/-
# Round 625: the certificate at `L = 9/4`, parts 1148–1155 of 1374

File 141 of 167: the parts `rows225C_1148` … `rows225C_1155` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (8 parts, 55499 depth-4 tests: row 163 columns 83–399, row 164 columns 0–55, row 164
columns 56–60, row 164 columns 61–64, row 164 columns 65–69, row 164 columns 70–75, row 164 columns 76–82, row 164
columns 83–399), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows225C_1148 : rowsJ 163 164 83 400 ≤ 538240052819394 := by decide +kernel

theorem rows225C_1149 : rowsJ 164 165 0 56 ≤ 63012731915237 := by decide +kernel

theorem rows225C_1150 : rowsJ 164 165 56 61 ≤ 19340418450562 := by decide +kernel

theorem rows225C_1151 : rowsJ 164 165 61 65 ≤ 20932650117585 := by decide +kernel

theorem rows225C_1152 : rowsJ 164 165 65 70 ≤ 15912666703241 := by decide +kernel

theorem rows225C_1153 : rowsJ 164 165 70 76 ≤ 7426951933327 := by decide +kernel

theorem rows225C_1154 : rowsJ 164 165 76 83 ≤ 1025360792922 := by decide +kernel

theorem rows225C_1155 : rowsJ 164 165 83 400 ≤ 643202933670033 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_1148
#print axioms SieveCert.rows225C_1155
