/-
# Round 625: the certificate at `L = 9/4`, parts 686–693 of 1374

File 85 of 167: the parts `rows225C_686` … `rows225C_693` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (8 parts, 55651 depth-4 tests: row 120 columns 86–88, row 120 columns 89–91, row 120
columns 92–94, row 120 columns 95–97, row 120 columns 98–101, row 120 columns 102–105, row 120 columns 106–109, row
120 columns 110–399), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows225C_686 : rowsJ 120 121 86 89 ≤ 0 := by decide +kernel

theorem rows225C_687 : rowsJ 120 121 89 92 ≤ 0 := by decide +kernel

theorem rows225C_688 : rowsJ 120 121 92 95 ≤ 0 := by decide +kernel

theorem rows225C_689 : rowsJ 120 121 95 98 ≤ 42623440116 := by decide +kernel

theorem rows225C_690 : rowsJ 120 121 98 102 ≤ 1188123838235 := by decide +kernel

theorem rows225C_691 : rowsJ 120 121 102 106 ≤ 4473790822942 := by decide +kernel

theorem rows225C_692 : rowsJ 120 121 106 110 ≤ 10086076101706 := by decide +kernel

theorem rows225C_693 : rowsJ 120 121 110 400 ≤ 622218440220162 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_686
#print axioms SieveCert.rows225C_693
