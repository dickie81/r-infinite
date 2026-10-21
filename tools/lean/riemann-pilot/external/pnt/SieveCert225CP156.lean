/-
# Round 625: the certificate at `L = 9/4`, parts 1270–1277 of 1374

File 156 of 167: the parts `rows225C_1270` … `rows225C_1277` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (8 parts, 55989 depth-4 tests: row 185 columns 61–399, row 186 columns 0–46, row 186
columns 47–52, row 186 columns 53–59, row 186 columns 60–399, row 187 columns 0–46, row 187 columns 47–52, row 187
columns 53–59), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows225C_1270 : rowsJ 185 186 61 400 ≤ 1917168997090107 := by decide +kernel

theorem rows225C_1271 : rowsJ 186 187 0 47 ≤ 27286200313769 := by decide +kernel

theorem rows225C_1272 : rowsJ 186 187 47 53 ≤ 40074175178628 := by decide +kernel

theorem rows225C_1273 : rowsJ 186 187 53 60 ≤ 30747345787667 := by decide +kernel

theorem rows225C_1274 : rowsJ 186 187 60 400 ≤ 1927845636970855 := by decide +kernel

theorem rows225C_1275 : rowsJ 187 188 0 47 ≤ 29958847967397 := by decide +kernel

theorem rows225C_1276 : rowsJ 187 188 47 53 ≤ 41247375938994 := by decide +kernel

theorem rows225C_1277 : rowsJ 187 188 53 60 ≤ 29131257486749 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_1270
#print axioms SieveCert.rows225C_1277
