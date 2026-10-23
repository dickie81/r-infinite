/-
# Round 625: the certificate at `L = 9/4`, parts 1312–1320 of 1374

File 161 of 167: the parts `rows225C_1312` … `rows225C_1320` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (9 parts, 56473 depth-4 tests: row 197 columns 43–50, row 197 columns 51–399, row 198
columns 0–42, row 198 columns 43–50, row 198 columns 51–399, row 199 columns 0–42, row 199 columns 43–50, row 199
columns 51–399, row 200 columns 0–41), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide
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

theorem rows225C_1312 : rowsJ 197 198 43 51 ≤ 60710810154229 := by decide +kernel

theorem rows225C_1313 : rowsJ 197 198 51 400 ≤ 2089533364896349 := by decide +kernel

theorem rows225C_1314 : rowsJ 198 199 0 43 ≤ 43475353925232 := by decide +kernel

theorem rows225C_1315 : rowsJ 198 199 43 51 ≤ 60741746918576 := by decide +kernel

theorem rows225C_1316 : rowsJ 198 199 51 400 ≤ 2099236531681313 := by decide +kernel

theorem rows225C_1317 : rowsJ 199 200 0 43 ≤ 47836250253389 := by decide +kernel

theorem rows225C_1318 : rowsJ 199 200 43 51 ≤ 60009824764514 := by decide +kernel

theorem rows225C_1319 : rowsJ 199 200 51 400 ≤ 2109182163319172 := by decide +kernel

theorem rows225C_1320 : rowsJ 200 201 0 42 ≤ 44112936028746 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_1312
#print axioms SieveCert.rows225C_1320
