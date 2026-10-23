/-
# Round 625: the certificate at `L = 9/4`, parts 1009–1017 of 1374

File 124 of 167: the parts `rows225C_1009` … `rows225C_1017` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (9 parts, 59801 depth-4 tests: row 147 columns 74–77, row 147 columns 78–81, row 147
columns 82–86, row 147 columns 87–92, row 147 columns 93–99, row 147 columns 100–399, row 148 columns 0–59, row 148
columns 60–65, row 148 columns 66–69), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide
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

theorem rows225C_1009 : rowsJ 147 148 74 78 ≤ 6559104276341 := by decide +kernel

theorem rows225C_1010 : rowsJ 147 148 78 82 ≤ 3000437523390 := by decide +kernel

theorem rows225C_1011 : rowsJ 147 148 82 87 ≤ 790168972875 := by decide +kernel

theorem rows225C_1012 : rowsJ 147 148 87 93 ≤ 0 := by decide +kernel

theorem rows225C_1013 : rowsJ 147 148 93 100 ≤ 4911817070561 := by decide +kernel

theorem rows225C_1014 : rowsJ 147 148 100 400 ≤ 513214222415923 := by decide +kernel

theorem rows225C_1015 : rowsJ 148 149 0 60 ≤ 143946727197790 := by decide +kernel

theorem rows225C_1016 : rowsJ 148 149 60 66 ≤ 11798147392496 := by decide +kernel

theorem rows225C_1017 : rowsJ 148 149 66 70 ≤ 12588174062337 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_1009
#print axioms SieveCert.rows225C_1017
