/-
# Round 625: the certificate at `L = 9/4`, parts 362–369 of 1374

File 45 of 167: the parts `rows225C_362` … `rows225C_369` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (8 parts, 55549 depth-4 tests: row 95 columns 92–94, row 95 columns 95–399, row 96 columns
0–34, row 96 columns 35–43, row 96 columns 44–50, row 96 columns 51–60, row 96 columns 61–81, row 96 columns 82–87),
each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid225C.lean`.
-/
import SieveGrid225C

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid225C

theorem rows225C_362 : rowsJ 95 96 92 95 ≤ 6112511748046 := by decide +kernel

theorem rows225C_363 : rowsJ 95 96 95 400 ≤ 2486324629275 := by decide +kernel

theorem rows225C_364 : rowsJ 96 97 0 35 ≤ 142651889479611 := by decide +kernel

theorem rows225C_365 : rowsJ 96 97 35 44 ≤ 94056834843314 := by decide +kernel

theorem rows225C_366 : rowsJ 96 97 44 51 ≤ 188161691053425 := by decide +kernel

theorem rows225C_367 : rowsJ 96 97 51 61 ≤ 226828711720341 := by decide +kernel

theorem rows225C_368 : rowsJ 96 97 61 82 ≤ 235953209120393 := by decide +kernel

theorem rows225C_369 : rowsJ 96 97 82 88 ≤ 19214578538555 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_362
#print axioms SieveCert.rows225C_369
