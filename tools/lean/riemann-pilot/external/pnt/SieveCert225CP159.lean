/-
# Round 625: the certificate at `L = 9/4`, parts 1296–1303 of 1374

File 159 of 167: the parts `rows225C_1296` … `rows225C_1303` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (8 parts, 52665 depth-4 tests: row 192 columns 45–51, row 192 columns 52–60, row 192
columns 61–399, row 193 columns 0–44, row 193 columns 45–51, row 193 columns 52–399, row 194 columns 0–43, row 194
columns 44–50), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows225C_1296 : rowsJ 192 193 45 52 ≤ 51390850714513 := by decide +kernel

theorem rows225C_1297 : rowsJ 192 193 52 61 ≤ 27896891621778 := by decide +kernel

theorem rows225C_1298 : rowsJ 192 193 61 400 ≤ 2004555647140383 := by decide +kernel

theorem rows225C_1299 : rowsJ 193 194 0 45 ≤ 37922506847213 := by decide +kernel

theorem rows225C_1300 : rowsJ 193 194 45 52 ≤ 51684749855491 := by decide +kernel

theorem rows225C_1301 : rowsJ 193 194 52 400 ≤ 2046648496704073 := by decide +kernel

theorem rows225C_1302 : rowsJ 194 195 0 44 ≤ 35017501693538 := by decide +kernel

theorem rows225C_1303 : rowsJ 194 195 44 51 ≤ 53090596703008 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_1296
#print axioms SieveCert.rows225C_1303
