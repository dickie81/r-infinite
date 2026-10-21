/-
# Round 625: the certificate at `L = 9/4`, parts 1188–1195 of 1374

File 146 of 167: the parts `rows225C_1188` … `rows225C_1195` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (8 parts, 56358 depth-4 tests: row 169 columns 77–399, row 170 columns 0–53, row 170
columns 54–58, row 170 columns 59–63, row 170 columns 64–69, row 170 columns 70–76, row 170 columns 77–399, row 171
columns 0–52), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows225C_1188 : rowsJ 169 170 77 400 ≤ 1145976936967844 := by decide +kernel

theorem rows225C_1189 : rowsJ 170 171 0 54 ≤ 45729778729456 := by decide +kernel

theorem rows225C_1190 : rowsJ 170 171 54 59 ≤ 23469951459043 := by decide +kernel

theorem rows225C_1191 : rowsJ 170 171 59 64 ≤ 25322023665246 := by decide +kernel

theorem rows225C_1192 : rowsJ 170 171 64 70 ≤ 14208602205267 := by decide +kernel

theorem rows225C_1193 : rowsJ 170 171 70 77 ≤ 3789834879750 := by decide +kernel

theorem rows225C_1194 : rowsJ 170 171 77 400 ≤ 1242023051939513 := by decide +kernel

theorem rows225C_1195 : rowsJ 171 172 0 53 ≤ 41632010643453 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_1188
#print axioms SieveCert.rows225C_1195
