/-
# Round 625: the certificate at `L = 9/4`, parts 149–156 of 1374

File 18 of 167: the parts `rows225C_149` … `rows225C_156` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (8 parts, 53187 depth-4 tests: row 68 columns 35–43, row 68 columns 44–49, row 68 columns
50–54, row 68 columns 55–58, row 68 columns 59–62, row 68 columns 63–66, row 68 columns 67–399, row 69 columns
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

theorem rows225C_149 : rowsJ 68 69 35 44 ≤ 115561843163722 := by decide +kernel

theorem rows225C_150 : rowsJ 68 69 44 50 ≤ 61397584065600 := by decide +kernel

theorem rows225C_151 : rowsJ 68 69 50 55 ≤ 84217776760841 := by decide +kernel

theorem rows225C_152 : rowsJ 68 69 55 59 ≤ 106861514961154 := by decide +kernel

theorem rows225C_153 : rowsJ 68 69 59 63 ≤ 144167320534358 := by decide +kernel

theorem rows225C_154 : rowsJ 68 69 63 67 ≤ 140657711319618 := by decide +kernel

theorem rows225C_155 : rowsJ 68 69 67 400 ≤ 66449506820794 := by decide +kernel

theorem rows225C_156 : rowsJ 69 70 0 35 ≤ 679213856321534 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_149
#print axioms SieveCert.rows225C_156
