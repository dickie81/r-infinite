/-
# Round 625: the certificate at `L = 9/4`, parts 1331–1339 of 1374

File 163 of 167: the parts `rows225C_1331` … `rows225C_1339` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (9 parts, 55903 depth-4 tests: row 203 columns 50–399, row 204 columns 0–40, row 204
columns 41–399, row 205 columns 0–40, row 205 columns 41–399, row 206 columns 0–39, row 206 columns 40–399, row 207
columns 0–39, row 207 columns 40–399), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide
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

theorem rows225C_1331 : rowsJ 203 204 50 400 ≤ 2154229981525761 := by decide +kernel

theorem rows225C_1332 : rowsJ 204 205 0 41 ≤ 53621619379705 := by decide +kernel

theorem rows225C_1333 : rowsJ 204 205 41 400 ≤ 2232324887652860 := by decide +kernel

theorem rows225C_1334 : rowsJ 205 206 0 41 ≤ 58675838217354 := by decide +kernel

theorem rows225C_1335 : rowsJ 205 206 41 400 ≤ 2240854871275719 := by decide +kernel

theorem rows225C_1336 : rowsJ 206 207 0 40 ≤ 53847530196478 := by decide +kernel

theorem rows225C_1337 : rowsJ 206 207 40 400 ≤ 2259518555566175 := by decide +kernel

theorem rows225C_1338 : rowsJ 207 208 0 40 ≤ 58924905680062 := by decide +kernel

theorem rows225C_1339 : rowsJ 207 208 40 400 ≤ 2267886767170914 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_1331
#print axioms SieveCert.rows225C_1339
