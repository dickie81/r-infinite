/-
# Round 625: the certificate at `L = 9/4`, parts 564–571 of 1374

File 70 of 167: the parts `rows225C_564` … `rows225C_571` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (8 parts, 59735 depth-4 tests: row 112 columns 46–73, row 112 columns 74–80, row 112
columns 81–84, row 112 columns 85–87, row 112 columns 88–90, row 112 columns 91–93, row 112 columns 94–96, row 112
columns 97–99), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows225C_564 : rowsJ 112 113 46 74 ≤ 246648518108469 := by decide +kernel

theorem rows225C_565 : rowsJ 112 113 74 81 ≤ 1770215160862 := by decide +kernel

theorem rows225C_566 : rowsJ 112 113 81 85 ≤ 14298897576 := by decide +kernel

theorem rows225C_567 : rowsJ 112 113 85 88 ≤ 459599836658 := by decide +kernel

theorem rows225C_568 : rowsJ 112 113 88 91 ≤ 1036970106777 := by decide +kernel

theorem rows225C_569 : rowsJ 112 113 91 94 ≤ 657503489978 := by decide +kernel

theorem rows225C_570 : rowsJ 112 113 94 97 ≤ 353591678785 := by decide +kernel

theorem rows225C_571 : rowsJ 112 113 97 100 ≤ 142679622009 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_564
#print axioms SieveCert.rows225C_571
