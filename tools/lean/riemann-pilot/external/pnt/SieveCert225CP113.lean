/-
# Round 625: the certificate at `L = 9/4`, parts 918–926 of 1374

File 113 of 167: the parts `rows225C_918` … `rows225C_926` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (9 parts, 59458 depth-4 tests: row 138 columns 87–90, row 138 columns 91–95, row 138
columns 96–101, row 138 columns 102–399, row 139 columns 0–60, row 139 columns 61–67, row 139 columns 68–71, row 139
columns 72–74, row 139 columns 75–77), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide
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

theorem rows225C_918 : rowsJ 138 139 87 91 ≤ 0 := by decide +kernel

theorem rows225C_919 : rowsJ 138 139 91 96 ≤ 0 := by decide +kernel

theorem rows225C_920 : rowsJ 138 139 96 102 ≤ 6867386748076 := by decide +kernel

theorem rows225C_921 : rowsJ 138 139 102 400 ≤ 997130256242297 := by decide +kernel

theorem rows225C_922 : rowsJ 139 140 0 61 ≤ 213301109108352 := by decide +kernel

theorem rows225C_923 : rowsJ 139 140 61 68 ≤ 6610985233274 := by decide +kernel

theorem rows225C_924 : rowsJ 139 140 68 72 ≤ 5369931102563 := by decide +kernel

theorem rows225C_925 : rowsJ 139 140 72 75 ≤ 3271471290173 := by decide +kernel

theorem rows225C_926 : rowsJ 139 140 75 78 ≤ 1409222426209 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_918
#print axioms SieveCert.rows225C_926
