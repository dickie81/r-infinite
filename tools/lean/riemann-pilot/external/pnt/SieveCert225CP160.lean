/-
# Round 625: the certificate at `L = 9/4`, parts 1304–1311 of 1374

File 160 of 167: the parts `rows225C_1304` … `rows225C_1311` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (8 parts, 55716 depth-4 tests: row 194 columns 51–399, row 195 columns 0–43, row 195
columns 44–50, row 195 columns 51–399, row 196 columns 0–43, row 196 columns 44–51, row 196 columns 52–399, row 197
columns 0–42), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows225C_1304 : rowsJ 194 195 51 400 ≤ 2061420769247079 := by decide +kernel

theorem rows225C_1305 : rowsJ 195 196 0 44 ≤ 38782069572965 := by decide +kernel

theorem rows225C_1306 : rowsJ 195 196 44 51 ≤ 53405247131379 := by decide +kernel

theorem rows225C_1307 : rowsJ 195 196 51 400 ≤ 2070628219038851 := by decide +kernel

theorem rows225C_1308 : rowsJ 196 197 0 44 ≤ 42669019682898 := by decide +kernel

theorem rows225C_1309 : rowsJ 196 197 44 52 ≤ 58745621715354 := by decide +kernel

theorem rows225C_1310 : rowsJ 196 197 52 400 ≤ 2074898922592637 := by decide +kernel

theorem rows225C_1311 : rowsJ 197 198 0 43 ≤ 39519122779497 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_1304
#print axioms SieveCert.rows225C_1311
