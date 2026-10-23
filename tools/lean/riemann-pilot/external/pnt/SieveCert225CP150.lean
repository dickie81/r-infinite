/-
# Round 625: the certificate at `L = 9/4`, parts 1221–1228 of 1374

File 150 of 167: the parts `rows225C_1221` … `rows225C_1228` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (8 parts, 58690 depth-4 tests: row 175 columns 58–63, row 175 columns 64–70, row 175
columns 71–399, row 176 columns 0–50, row 176 columns 51–56, row 176 columns 57–62, row 176 columns 63–69, row 176
columns 70–399), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows225C_1221 : rowsJ 175 176 58 64 ≤ 25542599218811 := by decide +kernel

theorem rows225C_1222 : rowsJ 175 176 64 71 ≤ 10223148238205 := by decide +kernel

theorem rows225C_1223 : rowsJ 175 176 71 400 ≤ 1711189676151016 := by decide +kernel

theorem rows225C_1224 : rowsJ 176 177 0 51 ≤ 31991818971815 := by decide +kernel

theorem rows225C_1225 : rowsJ 176 177 51 57 ≤ 32400570348125 := by decide +kernel

theorem rows225C_1226 : rowsJ 176 177 57 63 ≤ 27608947134684 := by decide +kernel

theorem rows225C_1227 : rowsJ 176 177 63 70 ≤ 11478397327424 := by decide +kernel

theorem rows225C_1228 : rowsJ 176 177 70 400 ≤ 1806962076279127 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_1221
#print axioms SieveCert.rows225C_1228
