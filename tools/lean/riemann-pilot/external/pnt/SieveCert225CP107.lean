/-
# Round 625: the certificate at `L = 9/4`, parts 867–874 of 1374

File 107 of 167: the parts `rows225C_867` … `rows225C_874` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (8 parts, 52421 depth-4 tests: row 134 columns 77–79, row 134 columns 80–82, row 134
columns 83–86, row 134 columns 87–90, row 134 columns 91–94, row 134 columns 95–99, row 134 columns 100–105, row 134
columns 106–399), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows225C_867 : rowsJ 134 135 77 80 ≤ 0 := by decide +kernel

theorem rows225C_868 : rowsJ 134 135 80 83 ≤ 0 := by decide +kernel

theorem rows225C_869 : rowsJ 134 135 83 87 ≤ 0 := by decide +kernel

theorem rows225C_870 : rowsJ 134 135 87 91 ≤ 0 := by decide +kernel

theorem rows225C_871 : rowsJ 134 135 91 95 ≤ 0 := by decide +kernel

theorem rows225C_872 : rowsJ 134 135 95 100 ≤ 2259075803667 := by decide +kernel

theorem rows225C_873 : rowsJ 134 135 100 106 ≤ 15023867748308 := by decide +kernel

theorem rows225C_874 : rowsJ 134 135 106 400 ≤ 1172464974989351 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_867
#print axioms SieveCert.rows225C_874
