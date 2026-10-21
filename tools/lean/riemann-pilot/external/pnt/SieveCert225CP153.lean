/-
# Round 625: the certificate at `L = 9/4`, parts 1245–1253 of 1374

File 153 of 167: the parts `rows225C_1245` … `rows225C_1253` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (9 parts, 57524 depth-4 tests: row 180 columns 50–55, row 180 columns 56–61, row 180
columns 62–69, row 180 columns 70–399, row 181 columns 0–48, row 181 columns 49–54, row 181 columns 55–60, row 181
columns 61–68, row 181 columns 69–399), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide
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

theorem rows225C_1245 : rowsJ 180 181 50 56 ≤ 36585820453723 := by decide +kernel

theorem rows225C_1246 : rowsJ 180 181 56 62 ≤ 25654263550576 := by decide +kernel

theorem rows225C_1247 : rowsJ 180 181 62 70 ≤ 10171884700333 := by decide +kernel

theorem rows225C_1248 : rowsJ 180 181 70 400 ≤ 1845983265935180 := by decide +kernel

theorem rows225C_1249 : rowsJ 181 182 0 49 ≤ 27651096719212 := by decide +kernel

theorem rows225C_1250 : rowsJ 181 182 49 55 ≤ 36017291755712 := by decide +kernel

theorem rows225C_1251 : rowsJ 181 182 55 61 ≤ 27862155483126 := by decide +kernel

theorem rows225C_1252 : rowsJ 181 182 61 69 ≤ 11608222324397 := by decide +kernel

theorem rows225C_1253 : rowsJ 181 182 69 400 ≤ 1859476532295000 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_1245
#print axioms SieveCert.rows225C_1253
