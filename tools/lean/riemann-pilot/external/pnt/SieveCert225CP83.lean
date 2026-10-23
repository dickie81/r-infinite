/-
# Round 625: the certificate at `L = 9/4`, parts 669–676 of 1374

File 83 of 167: the parts `rows225C_669` … `rows225C_676` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (8 parts, 56142 depth-4 tests: row 119 columns 80–82, row 119 columns 83–85, row 119
columns 86–88, row 119 columns 89–91, row 119 columns 92–94, row 119 columns 95–97, row 119 columns 98–101, row 119
columns 102–105), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows225C_669 : rowsJ 119 120 80 83 ≤ 0 := by decide +kernel

theorem rows225C_670 : rowsJ 119 120 83 86 ≤ 41308802393 := by decide +kernel

theorem rows225C_671 : rowsJ 119 120 86 89 ≤ 20821918307 := by decide +kernel

theorem rows225C_672 : rowsJ 119 120 89 92 ≤ 0 := by decide +kernel

theorem rows225C_673 : rowsJ 119 120 92 95 ≤ 0 := by decide +kernel

theorem rows225C_674 : rowsJ 119 120 95 98 ≤ 20892902782 := by decide +kernel

theorem rows225C_675 : rowsJ 119 120 98 102 ≤ 1001117720384 := by decide +kernel

theorem rows225C_676 : rowsJ 119 120 102 106 ≤ 4063768762350 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_669
#print axioms SieveCert.rows225C_676
