/-
# Round 625: the certificate at `L = 9/4`, parts 541–548 of 1374

File 67 of 167: the parts `rows225C_541` … `rows225C_548` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (8 parts, 53370 depth-4 tests: row 110 columns 91–93, row 110 columns 94–96, row 110
columns 97–99, row 110 columns 100–102, row 110 columns 103–105, row 110 columns 106–108, row 110 columns 109–399,
row 111 columns 0–34), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows225C_541 : rowsJ 110 111 91 94 ≤ 1221993683101 := by decide +kernel

theorem rows225C_542 : rowsJ 110 111 94 97 ≤ 798049774376 := by decide +kernel

theorem rows225C_543 : rowsJ 110 111 97 100 ≤ 459501919003 := by decide +kernel

theorem rows225C_544 : rowsJ 110 111 100 103 ≤ 245131223812 := by decide +kernel

theorem rows225C_545 : rowsJ 110 111 103 106 ≤ 783226663354 := by decide +kernel

theorem rows225C_546 : rowsJ 110 111 106 109 ≤ 2485575367621 := by decide +kernel

theorem rows225C_547 : rowsJ 110 111 109 400 ≤ 3099834405760 := by decide +kernel

theorem rows225C_548 : rowsJ 111 112 0 35 ≤ 62752904615144 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_541
#print axioms SieveCert.rows225C_548
