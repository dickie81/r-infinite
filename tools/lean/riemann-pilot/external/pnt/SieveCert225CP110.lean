/-
# Round 625: the certificate at `L = 9/4`, parts 892–900 of 1374

File 110 of 167: the parts `rows225C_892` … `rows225C_900` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (9 parts, 59970 depth-4 tests: row 136 columns 79–81, row 136 columns 82–85, row 136
columns 86–89, row 136 columns 90–93, row 136 columns 94–98, row 136 columns 99–104, row 136 columns 105–399, row
137 columns 0–60, row 137 columns 61–68), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide
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

theorem rows225C_892 : rowsJ 136 137 79 82 ≤ 0 := by decide +kernel

theorem rows225C_893 : rowsJ 136 137 82 86 ≤ 0 := by decide +kernel

theorem rows225C_894 : rowsJ 136 137 86 90 ≤ 0 := by decide +kernel

theorem rows225C_895 : rowsJ 136 137 90 94 ≤ 0 := by decide +kernel

theorem rows225C_896 : rowsJ 136 137 94 99 ≤ 1464980948894 := by decide +kernel

theorem rows225C_897 : rowsJ 136 137 99 105 ≤ 13659275973996 := by decide +kernel

theorem rows225C_898 : rowsJ 136 137 105 400 ≤ 1082300919751168 := by decide +kernel

theorem rows225C_899 : rowsJ 137 138 0 61 ≤ 230976559157568 := by decide +kernel

theorem rows225C_900 : rowsJ 137 138 61 69 ≤ 6050862224404 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_892
#print axioms SieveCert.rows225C_900
