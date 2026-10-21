/-
# Round 625: the certificate at `L = 9/4`, parts 818–825 of 1374

File 101 of 167: the parts `rows225C_818` … `rows225C_825` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (8 parts, 55143 depth-4 tests: row 130 columns 75–77, row 130 columns 78–80, row 130
columns 81–83, row 130 columns 84–86, row 130 columns 87–90, row 130 columns 91–94, row 130 columns 95–98, row 130
columns 99–103), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows225C_818 : rowsJ 130 131 75 78 ≤ 0 := by decide +kernel

theorem rows225C_819 : rowsJ 130 131 78 81 ≤ 0 := by decide +kernel

theorem rows225C_820 : rowsJ 130 131 81 84 ≤ 0 := by decide +kernel

theorem rows225C_821 : rowsJ 130 131 84 87 ≤ 0 := by decide +kernel

theorem rows225C_822 : rowsJ 130 131 87 91 ≤ 0 := by decide +kernel

theorem rows225C_823 : rowsJ 130 131 91 95 ≤ 0 := by decide +kernel

theorem rows225C_824 : rowsJ 130 131 95 99 ≤ 902314327959 := by decide +kernel

theorem rows225C_825 : rowsJ 130 131 99 104 ≤ 6934532078110 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_818
#print axioms SieveCert.rows225C_825
