/-
# Round 625: the certificate at `L = 9/4`, parts 1254–1261 of 1374

File 154 of 167: the parts `rows225C_1254` … `rows225C_1261` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (8 parts, 54411 depth-4 tests: row 182 columns 0–48, row 182 columns 49–54, row 182 columns
55–60, row 182 columns 61–68, row 182 columns 69–399, row 183 columns 0–48, row 183 columns 49–54, row 183 columns
55–61), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
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

theorem rows225C_1254 : rowsJ 182 183 0 49 ≤ 28861632106619 := by decide +kernel

theorem rows225C_1255 : rowsJ 182 183 49 55 ≤ 37696915235777 := by decide +kernel

theorem rows225C_1256 : rowsJ 182 183 55 61 ≤ 26424575950878 := by decide +kernel

theorem rows225C_1257 : rowsJ 182 183 61 69 ≤ 10475220777245 := by decide +kernel

theorem rows225C_1258 : rowsJ 182 183 69 400 ≤ 1872841883879814 := by decide +kernel

theorem rows225C_1259 : rowsJ 183 184 0 49 ≤ 30935857348514 := by decide +kernel

theorem rows225C_1260 : rowsJ 183 184 49 55 ≤ 38785887135942 := by decide +kernel

theorem rows225C_1261 : rowsJ 183 184 55 62 ≤ 27411820334584 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_1254
#print axioms SieveCert.rows225C_1261
