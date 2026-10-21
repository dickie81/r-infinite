/-
# Round 625: the certificate at `L = 9/4`, parts 261–268 of 1374

File 32 of 167: the parts `rows225C_261` … `rows225C_268` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (8 parts, 59925 depth-4 tests: row 82 columns 35–43, row 82 columns 44–49, row 82 columns
50–54, row 82 columns 55–60, row 82 columns 61–68, row 82 columns 69–399, row 83 columns 0–34, row 83 columns
35–43), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
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

theorem rows225C_261 : rowsJ 82 83 35 44 ≤ 37045027293768 := by decide +kernel

theorem rows225C_262 : rowsJ 82 83 44 50 ≤ 89823694601934 := by decide +kernel

theorem rows225C_263 : rowsJ 82 83 50 55 ≤ 145319184410678 := by decide +kernel

theorem rows225C_264 : rowsJ 82 83 55 61 ≤ 185107655876910 := by decide +kernel

theorem rows225C_265 : rowsJ 82 83 61 69 ≤ 207313032152918 := by decide +kernel

theorem rows225C_266 : rowsJ 82 83 69 400 ≤ 248686270450574 := by decide +kernel

theorem rows225C_267 : rowsJ 83 84 0 35 ≤ 362289025174691 := by decide +kernel

theorem rows225C_268 : rowsJ 83 84 35 44 ≤ 37323028244514 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_261
#print axioms SieveCert.rows225C_268
