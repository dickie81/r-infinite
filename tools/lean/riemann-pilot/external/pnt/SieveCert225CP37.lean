/-
# Round 625: the certificate at `L = 9/4`, parts 301–308 of 1374

File 37 of 167: the parts `rows225C_301` … `rows225C_308` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (8 parts, 56250 depth-4 tests: row 87 columns 78–399, row 88 columns 0–34, row 88 columns
35–43, row 88 columns 44–49, row 88 columns 50–55, row 88 columns 56–63, row 88 columns 64–79, row 88 columns
80–399), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
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

theorem rows225C_301 : rowsJ 87 88 78 400 ≤ 94102226047258 := by decide +kernel

theorem rows225C_302 : rowsJ 88 89 0 35 ≤ 263138847628921 := by decide +kernel

theorem rows225C_303 : rowsJ 88 89 35 44 ≤ 49725103300918 := by decide +kernel

theorem rows225C_304 : rowsJ 88 89 44 50 ≤ 124444584053973 := by decide +kernel

theorem rows225C_305 : rowsJ 88 89 50 56 ≤ 181037273335877 := by decide +kernel

theorem rows225C_306 : rowsJ 88 89 56 64 ≤ 203002321391111 := by decide +kernel

theorem rows225C_307 : rowsJ 88 89 64 80 ≤ 261798638544886 := by decide +kernel

theorem rows225C_308 : rowsJ 88 89 80 400 ≤ 71033403206441 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_301
#print axioms SieveCert.rows225C_308
