/-
# Round 625: the certificate at `L = 9/4`, parts 245–252 of 1374

File 30 of 167: the parts `rows225C_245` … `rows225C_252` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (8 parts, 54025 depth-4 tests: row 80 columns 35–43, row 80 columns 44–49, row 80 columns
50–54, row 80 columns 55–59, row 80 columns 60–66, row 80 columns 67–76, row 80 columns 77–399, row 81 columns
0–34), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
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

theorem rows225C_245 : rowsJ 80 81 35 44 ≤ 39112895639455 := by decide +kernel

theorem rows225C_246 : rowsJ 80 81 44 50 ≤ 79869596438528 := by decide +kernel

theorem rows225C_247 : rowsJ 80 81 50 55 ≤ 136035809989667 := by decide +kernel

theorem rows225C_248 : rowsJ 80 81 55 60 ≤ 162431999570711 := by decide +kernel

theorem rows225C_249 : rowsJ 80 81 60 67 ≤ 198425672307475 := by decide +kernel

theorem rows225C_250 : rowsJ 80 81 67 77 ≤ 222224121272314 := by decide +kernel

theorem rows225C_251 : rowsJ 80 81 77 400 ≤ 67865100716170 := by decide +kernel

theorem rows225C_252 : rowsJ 81 82 0 35 ≤ 405295136971662 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_245
#print axioms SieveCert.rows225C_252
