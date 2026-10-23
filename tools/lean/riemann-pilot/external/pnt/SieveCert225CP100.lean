/-
# Round 625: the certificate at `L = 9/4`, parts 810–817 of 1374

File 100 of 167: the parts `rows225C_810` … `rows225C_817` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (8 parts, 59980 depth-4 tests: row 129 columns 88–91, row 129 columns 92–95, row 129
columns 96–99, row 129 columns 100–104, row 129 columns 105–399, row 130 columns 0–37, row 130 columns 38–69, row
130 columns 70–74), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows225C_810 : rowsJ 129 130 88 92 ≤ 0 := by decide +kernel

theorem rows225C_811 : rowsJ 129 130 92 96 ≤ 0 := by decide +kernel

theorem rows225C_812 : rowsJ 129 130 96 100 ≤ 1519988687505 := by decide +kernel

theorem rows225C_813 : rowsJ 129 130 100 105 ≤ 8238875483861 := by decide +kernel

theorem rows225C_814 : rowsJ 129 130 105 400 ≤ 1357903324715829 := by decide +kernel

theorem rows225C_815 : rowsJ 130 131 0 38 ≤ 192607647042432 := by decide +kernel

theorem rows225C_816 : rowsJ 130 131 38 70 ≤ 107853302471338 := by decide +kernel

theorem rows225C_817 : rowsJ 130 131 70 75 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_810
#print axioms SieveCert.rows225C_817
