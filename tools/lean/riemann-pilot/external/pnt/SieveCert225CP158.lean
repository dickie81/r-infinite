/-
# Round 625: the certificate at `L = 9/4`, parts 1287–1295 of 1374

File 158 of 167: the parts `rows225C_1287` … `rows225C_1295` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (9 parts, 56019 depth-4 tests: row 190 columns 0–45, row 190 columns 46–52, row 190 columns
53–60, row 190 columns 61–399, row 191 columns 0–45, row 191 columns 46–52, row 191 columns 53–61, row 191 columns
62–399, row 192 columns 0–44), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide +kernel`, one
at a time (`Elab.async false`).

The file imports `SieveGrid225C.lean`.
-/
import SieveGrid225C

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid225C

theorem rows225C_1287 : rowsJ 190 191 0 46 ≤ 33347559346047 := by decide +kernel

theorem rows225C_1288 : rowsJ 190 191 46 53 ≤ 49768924281971 := by decide +kernel

theorem rows225C_1289 : rowsJ 190 191 53 61 ≤ 25831830258030 := by decide +kernel

theorem rows225C_1290 : rowsJ 190 191 61 400 ≤ 1978676254562061 := by decide +kernel

theorem rows225C_1291 : rowsJ 191 192 0 46 ≤ 36980928249111 := by decide +kernel

theorem rows225C_1292 : rowsJ 191 192 46 53 ≤ 50043370711126 := by decide +kernel

theorem rows225C_1293 : rowsJ 191 192 53 62 ≤ 25243760610248 := by decide +kernel

theorem rows225C_1294 : rowsJ 191 192 62 400 ≤ 1992988932134079 := by decide +kernel

theorem rows225C_1295 : rowsJ 192 193 0 45 ≤ 34223724653128 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_1287
#print axioms SieveCert.rows225C_1295
