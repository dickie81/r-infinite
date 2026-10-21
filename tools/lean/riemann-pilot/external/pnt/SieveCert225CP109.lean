/-
# Round 625: the certificate at `L = 9/4`, parts 883–891 of 1374

File 109 of 167: the parts `rows225C_883` … `rows225C_891` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (9 parts, 57449 depth-4 tests: row 135 columns 91–94, row 135 columns 95–99, row 135
columns 100–105, row 135 columns 106–399, row 136 columns 0–59, row 136 columns 60–68, row 136 columns 69–72, row
136 columns 73–75, row 136 columns 76–78), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide
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

theorem rows225C_883 : rowsJ 135 136 91 95 ≤ 0 := by decide +kernel

theorem rows225C_884 : rowsJ 135 136 95 100 ≤ 2449466659914 := by decide +kernel

theorem rows225C_885 : rowsJ 135 136 100 106 ≤ 15915801098080 := by decide +kernel

theorem rows225C_886 : rowsJ 135 136 106 400 ≤ 1076511581034231 := by decide +kernel

theorem rows225C_887 : rowsJ 136 137 0 60 ≤ 239567292201127 := by decide +kernel

theorem rows225C_888 : rowsJ 136 137 60 69 ≤ 5317627455269 := by decide +kernel

theorem rows225C_889 : rowsJ 136 137 69 73 ≤ 2892326475807 := by decide +kernel

theorem rows225C_890 : rowsJ 136 137 73 76 ≤ 639513993247 := by decide +kernel

theorem rows225C_891 : rowsJ 136 137 76 79 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_883
#print axioms SieveCert.rows225C_891
