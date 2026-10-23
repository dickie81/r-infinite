/-
# Round 625: the certificate at `L = 9/4`, parts 909–917 of 1374

File 112 of 167: the parts `rows225C_909` … `rows225C_917` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (9 parts, 58042 depth-4 tests: row 137 columns 100–105, row 137 columns 106–399, row 138
columns 0–60, row 138 columns 61–68, row 138 columns 69–72, row 138 columns 73–75, row 138 columns 76–78, row 138
columns 79–82, row 138 columns 83–86), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide
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

theorem rows225C_909 : rowsJ 137 138 100 106 ≤ 17712921872259 := by decide +kernel

theorem rows225C_910 : rowsJ 137 138 106 400 ≤ 981285177382543 := by decide +kernel

theorem rows225C_911 : rowsJ 138 139 0 61 ≤ 221602597898565 := by decide +kernel

theorem rows225C_912 : rowsJ 138 139 61 69 ≤ 6950161308745 := by decide +kernel

theorem rows225C_913 : rowsJ 138 139 69 73 ≤ 4413375760943 := by decide +kernel

theorem rows225C_914 : rowsJ 138 139 73 76 ≤ 2066490488725 := by decide +kernel

theorem rows225C_915 : rowsJ 138 139 76 79 ≤ 237587232622 := by decide +kernel

theorem rows225C_916 : rowsJ 138 139 79 83 ≤ 0 := by decide +kernel

theorem rows225C_917 : rowsJ 138 139 83 87 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_909
#print axioms SieveCert.rows225C_917
