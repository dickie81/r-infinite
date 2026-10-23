/-
# Round 625: the certificate at `L = 9/4`, parts 1213–1220 of 1374

File 149 of 167: the parts `rows225C_1213` … `rows225C_1220` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (8 parts, 54405 depth-4 tests: row 174 columns 0–51, row 174 columns 52–57, row 174 columns
58–62, row 174 columns 63–68, row 174 columns 69–76, row 174 columns 77–399, row 175 columns 0–51, row 175 columns
52–57), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
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

theorem rows225C_1213 : rowsJ 174 175 0 52 ≤ 35887340709869 := by decide +kernel

theorem rows225C_1214 : rowsJ 174 175 52 58 ≤ 31483432848737 := by decide +kernel

theorem rows225C_1215 : rowsJ 174 175 58 63 ≤ 23722122831012 := by decide +kernel

theorem rows225C_1216 : rowsJ 174 175 63 69 ≤ 12624971020095 := by decide +kernel

theorem rows225C_1217 : rowsJ 174 175 69 77 ≤ 2822164866351 := by decide +kernel

theorem rows225C_1218 : rowsJ 174 175 77 400 ≤ 1614647828143790 := by decide +kernel

theorem rows225C_1219 : rowsJ 175 176 0 52 ≤ 36066837837080 := by decide +kernel

theorem rows225C_1220 : rowsJ 175 176 52 58 ≤ 32985255906168 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_1213
#print axioms SieveCert.rows225C_1220
