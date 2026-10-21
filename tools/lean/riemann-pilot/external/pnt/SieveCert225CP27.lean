/-
# Round 625: the certificate at `L = 9/4`, parts 221–228 of 1374

File 27 of 167: the parts `rows225C_221` … `rows225C_228` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (8 parts, 55595 depth-4 tests: row 77 columns 35–43, row 77 columns 44–49, row 77 columns
50–54, row 77 columns 55–59, row 77 columns 60–65, row 77 columns 66–73, row 77 columns 74–399, row 78 columns
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

theorem rows225C_221 : rowsJ 77 78 35 44 ≤ 48348271700745 := by decide +kernel

theorem rows225C_222 : rowsJ 77 78 44 50 ≤ 67753518757659 := by decide +kernel

theorem rows225C_223 : rowsJ 77 78 50 55 ≤ 119848228245897 := by decide +kernel

theorem rows225C_224 : rowsJ 77 78 55 60 ≤ 168592431126976 := by decide +kernel

theorem rows225C_225 : rowsJ 77 78 60 66 ≤ 184096956296124 := by decide +kernel

theorem rows225C_226 : rowsJ 77 78 66 74 ≤ 206617893574721 := by decide +kernel

theorem rows225C_227 : rowsJ 77 78 74 400 ≤ 85942454539948 := by decide +kernel

theorem rows225C_228 : rowsJ 78 79 0 35 ≤ 472089346307203 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_221
#print axioms SieveCert.rows225C_228
