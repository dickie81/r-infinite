/-
# Round 625: the certificate at `L = 9/4`, parts 556–563 of 1374

File 69 of 167: the parts `rows225C_556` … `rows225C_563` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (8 parts, 54324 depth-4 tests: row 111 columns 94–96, row 111 columns 97–99, row 111
columns 100–102, row 111 columns 103–105, row 111 columns 106–109, row 111 columns 110–399, row 112 columns 0–34,
row 112 columns 35–45), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide +kernel`, one at a
time (`Elab.async false`).

The file imports `SieveGrid225C.lean`.
-/
import SieveGrid225C

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid225C

theorem rows225C_556 : rowsJ 111 112 94 97 ≤ 553332357586 := by decide +kernel

theorem rows225C_557 : rowsJ 111 112 97 100 ≤ 278292086653 := by decide +kernel

theorem rows225C_558 : rowsJ 111 112 100 103 ≤ 187378103049 := by decide +kernel

theorem rows225C_559 : rowsJ 111 112 103 106 ≤ 980201228688 := by decide +kernel

theorem rows225C_560 : rowsJ 111 112 106 110 ≤ 4443390990652 := by decide +kernel

theorem rows225C_561 : rowsJ 111 112 110 400 ≤ 4174419605166 := by decide +kernel

theorem rows225C_562 : rowsJ 112 113 0 35 ≤ 63872230009065 := by decide +kernel

theorem rows225C_563 : rowsJ 112 113 35 46 ≤ 227094084483930 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_556
#print axioms SieveCert.rows225C_563
