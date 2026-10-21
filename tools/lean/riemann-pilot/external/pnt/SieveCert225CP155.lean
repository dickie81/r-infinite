/-
# Round 625: the certificate at `L = 9/4`, parts 1262–1269 of 1374

File 155 of 167: the parts `rows225C_1262` … `rows225C_1269` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (8 parts, 59335 depth-4 tests: row 183 columns 62–399, row 184 columns 0–47, row 184
columns 48–53, row 184 columns 54–60, row 184 columns 61–399, row 185 columns 0–47, row 185 columns 48–53, row 185
columns 54–60), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows225C_1262 : rowsJ 183 184 62 400 ≤ 1888453632879381 := by decide +kernel

theorem rows225C_1263 : rowsJ 184 185 0 48 ≤ 27786198381737 := by decide +kernel

theorem rows225C_1264 : rowsJ 184 185 48 54 ≤ 38858749264448 := by decide +kernel

theorem rows225C_1265 : rowsJ 184 185 54 61 ≤ 29825538215764 := by decide +kernel

theorem rows225C_1266 : rowsJ 184 185 61 400 ≤ 1903780712626085 := by decide +kernel

theorem rows225C_1267 : rowsJ 185 186 0 48 ≤ 30146221045030 := by decide +kernel

theorem rows225C_1268 : rowsJ 185 186 48 54 ≤ 39988770271848 := by decide +kernel

theorem rows225C_1269 : rowsJ 185 186 54 61 ≤ 28252258323385 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_1262
#print axioms SieveCert.rows225C_1269
