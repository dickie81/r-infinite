/-
# Round 625: the certificate at `L = 9/4`, parts 1321–1330 of 1374

File 162 of 167: the parts `rows225C_1321` … `rows225C_1330` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (10 parts, 57775 depth-4 tests: row 200 columns 42–49, row 200 columns 50–399, row 201
columns 0–41, row 201 columns 42–50, row 201 columns 51–399, row 202 columns 0–41, row 202 columns 42–50, row 202
columns 51–399, row 203 columns 0–40, row 203 columns 41–49), each a sum of costs (`rows` or `rowsJ`) at most its
bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid225C.lean`.
-/
import SieveGrid225C

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid225C

theorem rows225C_1321 : rowsJ 200 201 42 50 ≤ 62836641357174 := by decide +kernel

theorem rows225C_1322 : rowsJ 200 201 50 400 ≤ 2123891785921863 := by decide +kernel

theorem rows225C_1323 : rowsJ 201 202 0 42 ≤ 48523060650734 := by decide +kernel

theorem rows225C_1324 : rowsJ 201 202 42 51 ≤ 66478602462089 := by decide +kernel

theorem rows225C_1325 : rowsJ 201 202 51 400 ≤ 2129494420672516 := by decide +kernel

theorem rows225C_1326 : rowsJ 202 203 0 42 ≤ 53108317265383 := by decide +kernel

theorem rows225C_1327 : rowsJ 202 203 42 51 ≤ 65413361732151 := by decide +kernel

theorem rows225C_1328 : rowsJ 202 203 51 400 ≤ 2139863594423713 := by decide +kernel

theorem rows225C_1329 : rowsJ 203 204 0 41 ≤ 48986127760364 := by decide +kernel

theorem rows225C_1330 : rowsJ 203 204 41 50 ≤ 68819766857839 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_1321
#print axioms SieveCert.rows225C_1330
