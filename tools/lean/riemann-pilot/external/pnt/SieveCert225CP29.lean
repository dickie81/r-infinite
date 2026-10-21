/-
# Round 625: the certificate at `L = 9/4`, parts 237–244 of 1374

File 29 of 167: the parts `rows225C_237` … `rows225C_244` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (8 parts, 54660 depth-4 tests: row 79 columns 35–43, row 79 columns 44–49, row 79 columns
50–54, row 79 columns 55–59, row 79 columns 60–65, row 79 columns 66–74, row 79 columns 75–399, row 80 columns
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

theorem rows225C_237 : rowsJ 79 80 35 44 ≤ 41429388654620 := by decide +kernel

theorem rows225C_238 : rowsJ 79 80 44 50 ≤ 75372014145877 := by decide +kernel

theorem rows225C_239 : rowsJ 79 80 50 55 ≤ 130558423134235 := by decide +kernel

theorem rows225C_240 : rowsJ 79 80 55 60 ≤ 165644374352804 := by decide +kernel

theorem rows225C_241 : rowsJ 79 80 60 66 ≤ 176177989772505 := by decide +kernel

theorem rows225C_242 : rowsJ 79 80 66 75 ≤ 216466220743666 := by decide +kernel

theorem rows225C_243 : rowsJ 79 80 75 400 ≤ 94232928447454 := by decide +kernel

theorem rows225C_244 : rowsJ 80 81 0 35 ≤ 427307565258930 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_237
#print axioms SieveCert.rows225C_244
