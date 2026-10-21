/-
# Round 625: the certificate at `L = 9/4`, parts 653–660 of 1374

File 81 of 167: the parts `rows225C_653` … `rows225C_660` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (8 parts, 53490 depth-4 tests: row 118 columns 76–79, row 118 columns 80–82, row 118
columns 83–85, row 118 columns 86–88, row 118 columns 89–91, row 118 columns 92–94, row 118 columns 95–97, row 118
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

theorem rows225C_653 : rowsJ 118 119 76 80 ≤ 0 := by decide +kernel

theorem rows225C_654 : rowsJ 118 119 80 83 ≤ 0 := by decide +kernel

theorem rows225C_655 : rowsJ 118 119 83 86 ≤ 75227806466 := by decide +kernel

theorem rows225C_656 : rowsJ 118 119 86 89 ≤ 83521146617 := by decide +kernel

theorem rows225C_657 : rowsJ 118 119 89 92 ≤ 7063458009 := by decide +kernel

theorem rows225C_658 : rowsJ 118 119 92 95 ≤ 0 := by decide +kernel

theorem rows225C_659 : rowsJ 118 119 95 98 ≤ 0 := by decide +kernel

theorem rows225C_660 : rowsJ 118 119 98 101 ≤ 398288908119 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_653
#print axioms SieveCert.rows225C_660
