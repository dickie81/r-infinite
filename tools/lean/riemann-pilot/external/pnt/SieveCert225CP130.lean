/-
# Round 625: the certificate at `L = 9/4`, parts 1058–1065 of 1374

File 130 of 167: the parts `rows225C_1058` … `rows225C_1065` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (8 parts, 54055 depth-4 tests: row 152 columns 88–94, row 152 columns 95–399, row 153
columns 0–58, row 153 columns 59–64, row 153 columns 65–68, row 153 columns 69–72, row 153 columns 73–76, row 153
columns 77–81), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows225C_1058 : rowsJ 152 153 88 95 ≤ 0 := by decide +kernel

theorem rows225C_1059 : rowsJ 152 153 95 400 ≤ 315369991478012 := by decide +kernel

theorem rows225C_1060 : rowsJ 153 154 0 59 ≤ 113472352390786 := by decide +kernel

theorem rows225C_1061 : rowsJ 153 154 59 65 ≤ 15734536017835 := by decide +kernel

theorem rows225C_1062 : rowsJ 153 154 65 69 ≤ 16625325185171 := by decide +kernel

theorem rows225C_1063 : rowsJ 153 154 69 73 ≤ 12993839489014 := by decide +kernel

theorem rows225C_1064 : rowsJ 153 154 73 77 ≤ 7570903657053 := by decide +kernel

theorem rows225C_1065 : rowsJ 153 154 77 82 ≤ 4100990942948 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_1058
#print axioms SieveCert.rows225C_1065
