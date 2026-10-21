/-
# Round 625: the certificate at `L = 9/4`, parts 470–477 of 1374

File 58 of 167: the parts `rows225C_470` … `rows225C_477` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (8 parts, 54978 depth-4 tests: row 105 columns 56–78, row 105 columns 79–83, row 105
columns 84–87, row 105 columns 88–90, row 105 columns 91–92, row 105 columns 93–94, row 105 columns 95–97, row 105
columns 98–100), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide +kernel`, one at a time
(`Elab.async false`).

The file imports `SieveGrid225C.lean`.
-/
import SieveGrid225C

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid225C

theorem rows225C_470 : rowsJ 105 106 56 79 ≤ 188358761234542 := by decide +kernel

theorem rows225C_471 : rowsJ 105 106 79 84 ≤ 4452765734361 := by decide +kernel

theorem rows225C_472 : rowsJ 105 106 84 88 ≤ 585835170988 := by decide +kernel

theorem rows225C_473 : rowsJ 105 106 88 91 ≤ 1803474085909 := by decide +kernel

theorem rows225C_474 : rowsJ 105 106 91 93 ≤ 2177213796512 := by decide +kernel

theorem rows225C_475 : rowsJ 105 106 93 95 ≤ 2026218388380 := by decide +kernel

theorem rows225C_476 : rowsJ 105 106 95 98 ≤ 2475797855363 := by decide +kernel

theorem rows225C_477 : rowsJ 105 106 98 101 ≤ 1857177535439 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_470
#print axioms SieveCert.rows225C_477
