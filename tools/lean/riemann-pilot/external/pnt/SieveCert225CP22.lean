/-
# Round 625: the certificate at `L = 9/4`, parts 181–188 of 1374

File 22 of 167: the parts `rows225C_181` … `rows225C_188` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (8 parts, 55765 depth-4 tests: row 72 columns 35–43, row 72 columns 44–49, row 72 columns
50–54, row 72 columns 55–58, row 72 columns 59–62, row 72 columns 63–67, row 72 columns 68–399, row 73 columns
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

theorem rows225C_181 : rowsJ 72 73 35 44 ≤ 78722142172419 := by decide +kernel

theorem rows225C_182 : rowsJ 72 73 44 50 ≤ 58625030563892 := by decide +kernel

theorem rows225C_183 : rowsJ 72 73 50 55 ≤ 96177582530141 := by decide +kernel

theorem rows225C_184 : rowsJ 72 73 55 59 ≤ 123790380810143 := by decide +kernel

theorem rows225C_185 : rowsJ 72 73 59 63 ≤ 140906452920930 := by decide +kernel

theorem rows225C_186 : rowsJ 72 73 63 68 ≤ 161323348361838 := by decide +kernel

theorem rows225C_187 : rowsJ 72 73 68 400 ≤ 144600031093641 := by decide +kernel

theorem rows225C_188 : rowsJ 73 74 0 35 ≤ 586827681061417 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_181
#print axioms SieveCert.rows225C_188
