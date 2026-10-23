/-
# Round 625: the certificate at `L = 9/4`, parts 851–858 of 1374

File 105 of 167: the parts `rows225C_851` … `rows225C_858` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (8 parts, 54839 depth-4 tests: row 133 columns 0–42, row 133 columns 43–69, row 133 columns
70–73, row 133 columns 74–76, row 133 columns 77–79, row 133 columns 80–82, row 133 columns 83–85, row 133 columns
86–89), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
false`).

The file imports `SieveGrid225C.lean`.
-/
import SieveGrid225C

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid225C

theorem rows225C_851 : rowsJ 133 134 0 43 ≤ 232669166923485 := by decide +kernel

theorem rows225C_852 : rowsJ 133 134 43 70 ≤ 39663081176814 := by decide +kernel

theorem rows225C_853 : rowsJ 133 134 70 74 ≤ 458647690018 := by decide +kernel

theorem rows225C_854 : rowsJ 133 134 74 77 ≤ 0 := by decide +kernel

theorem rows225C_855 : rowsJ 133 134 77 80 ≤ 0 := by decide +kernel

theorem rows225C_856 : rowsJ 133 134 80 83 ≤ 0 := by decide +kernel

theorem rows225C_857 : rowsJ 133 134 83 86 ≤ 0 := by decide +kernel

theorem rows225C_858 : rowsJ 133 134 86 90 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_851
#print axioms SieveCert.rows225C_858
