/-
# Round 625: the certificate at `L = 9/4`, parts 1278–1286 of 1374

File 157 of 167: the parts `rows225C_1278` … `rows225C_1286` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (9 parts, 57291 depth-4 tests: row 187 columns 60–399, row 188 columns 0–46, row 188
columns 47–52, row 188 columns 53–60, row 188 columns 61–399, row 189 columns 0–45, row 189 columns 46–52, row 189
columns 53–60, row 189 columns 61–399), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide
+kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid225C.lean`.
-/
import SieveGrid225C

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid225C

theorem rows225C_1278 : rowsJ 187 188 60 400 ≤ 1941778262257410 := by decide +kernel

theorem rows225C_1279 : rowsJ 188 189 0 47 ≤ 32702289023606 := by decide +kernel

theorem rows225C_1280 : rowsJ 188 189 47 53 ≤ 42431233515555 := by decide +kernel

theorem rows225C_1281 : rowsJ 188 189 53 61 ≤ 29333857208635 := by decide +kernel

theorem rows225C_1282 : rowsJ 188 189 61 400 ≤ 1954071518363482 := by decide +kernel

theorem rows225C_1283 : rowsJ 189 190 0 46 ≤ 30259219367295 := by decide +kernel

theorem rows225C_1284 : rowsJ 189 190 46 53 ≤ 48826852543330 := by decide +kernel

theorem rows225C_1285 : rowsJ 189 190 53 61 ≤ 27611129593893 := by decide +kernel

theorem rows225C_1286 : rowsJ 189 190 61 400 ≤ 1963621425113902 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_1278
#print axioms SieveCert.rows225C_1286
