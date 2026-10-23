/-
# Round 625: the certificate at `L = 9/4`, parts 826–833 of 1374

File 102 of 167: the parts `rows225C_826` … `rows225C_833` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (8 parts, 56556 depth-4 tests: row 130 columns 104–399, row 131 columns 0–38, row 131
columns 39–69, row 131 columns 70–74, row 131 columns 75–77, row 131 columns 78–80, row 131 columns 81–83, row 131
columns 84–86), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows225C_826 : rowsJ 130 131 104 400 ≤ 1363403079994764 := by decide +kernel

theorem rows225C_827 : rowsJ 131 132 0 39 ≤ 204226516077255 := by decide +kernel

theorem rows225C_828 : rowsJ 131 132 39 70 ≤ 86897520581550 := by decide +kernel

theorem rows225C_829 : rowsJ 131 132 70 75 ≤ 0 := by decide +kernel

theorem rows225C_830 : rowsJ 131 132 75 78 ≤ 0 := by decide +kernel

theorem rows225C_831 : rowsJ 131 132 78 81 ≤ 0 := by decide +kernel

theorem rows225C_832 : rowsJ 131 132 81 84 ≤ 0 := by decide +kernel

theorem rows225C_833 : rowsJ 131 132 84 87 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_826
#print axioms SieveCert.rows225C_833
