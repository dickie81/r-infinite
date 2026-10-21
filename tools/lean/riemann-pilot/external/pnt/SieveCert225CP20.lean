/-
# Round 625: the certificate at `L = 9/4`, parts 165–172 of 1374

File 20 of 167: the parts `rows225C_165` … `rows225C_172` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (8 parts, 54815 depth-4 tests: row 70 columns 35–43, row 70 columns 44–49, row 70 columns
50–54, row 70 columns 55–58, row 70 columns 59–62, row 70 columns 63–67, row 70 columns 68–399, row 71 columns
0–34), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
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

theorem rows225C_165 : rowsJ 70 71 35 44 ≤ 95808024355616 := by decide +kernel

theorem rows225C_166 : rowsJ 70 71 44 50 ≤ 58930927628355 := by decide +kernel

theorem rows225C_167 : rowsJ 70 71 50 55 ≤ 89273768187565 := by decide +kernel

theorem rows225C_168 : rowsJ 70 71 55 59 ≤ 114996294467008 := by decide +kernel

theorem rows225C_169 : rowsJ 70 71 59 63 ≤ 144271549518907 := by decide +kernel

theorem rows225C_170 : rowsJ 70 71 63 68 ≤ 167786658112131 := by decide +kernel

theorem rows225C_171 : rowsJ 70 71 68 400 ≤ 92795058903449 := by decide +kernel

theorem rows225C_172 : rowsJ 71 72 0 35 ≤ 633095511510787 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_165
#print axioms SieveCert.rows225C_172
