/-
# Round 625: the certificate at `L = 9/4`, parts 394–401 of 1374

File 49 of 167: the parts `rows225C_394` … `rows225C_401` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (8 parts, 56445 depth-4 tests: row 99 columns 35–43, row 99 columns 44–51, row 99 columns
52–65, row 99 columns 66–83, row 99 columns 84–87, row 99 columns 88–90, row 99 columns 91–93, row 99 columns
94–95), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
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

theorem rows225C_394 : rowsJ 99 100 35 44 ≤ 115844633864499 := by decide +kernel

theorem rows225C_395 : rowsJ 99 100 44 52 ≤ 210459325140970 := by decide +kernel

theorem rows225C_396 : rowsJ 99 100 52 66 ≤ 253836341258898 := by decide +kernel

theorem rows225C_397 : rowsJ 99 100 66 84 ≤ 127461909827140 := by decide +kernel

theorem rows225C_398 : rowsJ 99 100 84 88 ≤ 6119407101628 := by decide +kernel

theorem rows225C_399 : rowsJ 99 100 88 91 ≤ 2759331535723 := by decide +kernel

theorem rows225C_400 : rowsJ 99 100 91 94 ≤ 4143379304102 := by decide +kernel

theorem rows225C_401 : rowsJ 99 100 94 96 ≤ 4205200469413 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_394
#print axioms SieveCert.rows225C_401
