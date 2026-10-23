/-
# Round 625: the certificate at `L = 9/4`, parts 1350–1359 of 1374

File 165 of 167: the parts `rows225C_1350` … `rows225C_1359` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (10 parts, 53986 depth-4 tests: row 213 columns 0–38, row 213 columns 39–399, row 214
columns 0–37, row 214 columns 38–399, row 215 columns 0–37, row 215 columns 38–399, rows 216–216, rows 217–217, rows
218–218, rows 219–219), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide +kernel`, one at a
time (`Elab.async false`).

The file imports `SieveGrid225C.lean`.
-/
import SieveGrid225C

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid225C

theorem rows225C_1350 : rowsJ 213 214 0 39 ≤ 81286441426904 := by decide +kernel

theorem rows225C_1351 : rowsJ 213 214 39 400 ≤ 2739527703325721 := by decide +kernel

theorem rows225C_1352 : rowsJ 214 215 0 38 ≤ 75395955044319 := by decide +kernel

theorem rows225C_1353 : rowsJ 214 215 38 400 ≤ 2833083850062326 := by decide +kernel

theorem rows225C_1354 : rowsJ 215 216 0 38 ≤ 80629535567457 := by decide +kernel

theorem rows225C_1355 : rowsJ 215 216 38 400 ≤ 2914550542038376 := by decide +kernel

theorem rows225C_1356 : rows 216 217 ≤ 3081928255582647 := by decide +kernel

theorem rows225C_1357 : rows 217 218 ≤ 3167566062667082 := by decide +kernel

theorem rows225C_1358 : rows 218 219 ≤ 3253220884056445 := by decide +kernel

theorem rows225C_1359 : rows 219 220 ≤ 3337807803271098 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_1350
#print axioms SieveCert.rows225C_1359
