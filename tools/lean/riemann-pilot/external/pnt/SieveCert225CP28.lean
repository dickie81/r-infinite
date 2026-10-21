/-
# Round 625: the certificate at `L = 9/4`, parts 229–236 of 1374

File 28 of 167: the parts `rows225C_229` … `rows225C_236` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (8 parts, 55167 depth-4 tests: row 78 columns 35–43, row 78 columns 44–49, row 78 columns
50–54, row 78 columns 55–59, row 78 columns 60–65, row 78 columns 66–73, row 78 columns 74–399, row 79 columns
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

theorem rows225C_229 : rowsJ 78 79 35 44 ≤ 44467417842081 := by decide +kernel

theorem rows225C_230 : rowsJ 78 79 44 50 ≤ 71326314927059 := by decide +kernel

theorem rows225C_231 : rowsJ 78 79 50 55 ≤ 125188546111372 := by decide +kernel

theorem rows225C_232 : rowsJ 78 79 55 60 ≤ 167127584413615 := by decide +kernel

theorem rows225C_233 : rowsJ 78 79 60 66 ≤ 180150469886759 := by decide +kernel

theorem rows225C_234 : rowsJ 78 79 66 74 ≤ 201010155544975 := by decide +kernel

theorem rows225C_235 : rowsJ 78 79 74 400 ≤ 101796530335118 := by decide +kernel

theorem rows225C_236 : rowsJ 79 80 0 35 ≤ 449565164155789 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_229
#print axioms SieveCert.rows225C_236
