/-
# Round 625: the certificate at `L = 9/4`, parts 39–46 of 1374

File 5 of 167: the parts `rows225C_39` … `rows225C_46` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (8 parts, 55605 depth-4 tests: row 47 columns 0–34, row 47 columns 35–43, row 47 columns
44–399, row 48 columns 0–34, row 48 columns 35–43, row 48 columns 44–399, row 49 columns 0–34, row 49 columns
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

theorem rows225C_39 : rowsJ 47 48 0 35 ≤ 1111655404866908 := by decide +kernel

theorem rows225C_40 : rowsJ 47 48 35 44 ≤ 463514356899250 := by decide +kernel

theorem rows225C_41 : rowsJ 47 48 44 400 ≤ 146521944475731 := by decide +kernel

theorem rows225C_42 : rowsJ 48 49 0 35 ≤ 1095903370651146 := by decide +kernel

theorem rows225C_43 : rowsJ 48 49 35 44 ≤ 442689972321614 := by decide +kernel

theorem rows225C_44 : rowsJ 48 49 44 400 ≤ 168227421896214 := by decide +kernel

theorem rows225C_45 : rowsJ 49 50 0 35 ≤ 1079860163343374 := by decide +kernel

theorem rows225C_46 : rowsJ 49 50 35 44 ≤ 422039552049378 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_39
#print axioms SieveCert.rows225C_46
