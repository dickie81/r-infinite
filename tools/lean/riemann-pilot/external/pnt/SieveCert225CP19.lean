/-
# Round 625: the certificate at `L = 9/4`, parts 157–164 of 1374

File 19 of 167: the parts `rows225C_157` … `rows225C_164` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (8 parts, 54105 depth-4 tests: row 69 columns 35–43, row 69 columns 44–49, row 69 columns
50–54, row 69 columns 55–58, row 69 columns 59–62, row 69 columns 63–67, row 69 columns 68–399, row 70 columns
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

theorem rows225C_157 : rowsJ 69 70 35 44 ≤ 105397387894416 := by decide +kernel

theorem rows225C_158 : rowsJ 69 70 44 50 ≤ 59899130225253 := by decide +kernel

theorem rows225C_159 : rowsJ 69 70 50 55 ≤ 86465388745745 := by decide +kernel

theorem rows225C_160 : rowsJ 69 70 55 59 ≤ 110802784635251 := by decide +kernel

theorem rows225C_161 : rowsJ 69 70 59 63 ≤ 145071816834436 := by decide +kernel

theorem rows225C_162 : rowsJ 69 70 63 68 ≤ 171016744681613 := by decide +kernel

theorem rows225C_163 : rowsJ 69 70 68 400 ≤ 63837110186720 := by decide +kernel

theorem rows225C_164 : rowsJ 70 71 0 35 ≤ 656239900510484 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_157
#print axioms SieveCert.rows225C_164
