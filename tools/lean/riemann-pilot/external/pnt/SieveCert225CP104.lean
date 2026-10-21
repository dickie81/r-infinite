/-
# Round 625: the certificate at `L = 9/4`, parts 842–850 of 1374

File 104 of 167: the parts `rows225C_842` … `rows225C_850` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (9 parts, 59770 depth-4 tests: row 132 columns 75–77, row 132 columns 78–80, row 132
columns 81–83, row 132 columns 84–86, row 132 columns 87–90, row 132 columns 91–94, row 132 columns 95–99, row 132
columns 100–104, row 132 columns 105–399), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide
+kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid225C.lean`.
-/
import SieveGrid225C

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid225C

theorem rows225C_842 : rowsJ 132 133 75 78 ≤ 0 := by decide +kernel

theorem rows225C_843 : rowsJ 132 133 78 81 ≤ 0 := by decide +kernel

theorem rows225C_844 : rowsJ 132 133 81 84 ≤ 0 := by decide +kernel

theorem rows225C_845 : rowsJ 132 133 84 87 ≤ 0 := by decide +kernel

theorem rows225C_846 : rowsJ 132 133 87 91 ≤ 0 := by decide +kernel

theorem rows225C_847 : rowsJ 132 133 91 95 ≤ 0 := by decide +kernel

theorem rows225C_848 : rowsJ 132 133 95 100 ≤ 1941126236130 := by decide +kernel

theorem rows225C_849 : rowsJ 132 133 100 105 ≤ 9946453127060 := by decide +kernel

theorem rows225C_850 : rowsJ 132 133 105 400 ≤ 1269111118061258 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_842
#print axioms SieveCert.rows225C_850
