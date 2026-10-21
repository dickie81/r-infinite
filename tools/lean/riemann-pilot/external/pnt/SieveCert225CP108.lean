/-
# Round 625: the certificate at `L = 9/4`, parts 875–882 of 1374

File 108 of 167: the parts `rows225C_875` … `rows225C_882` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (8 parts, 56677 depth-4 tests: row 135 columns 0–59, row 135 columns 60–68, row 135 columns
69–73, row 135 columns 74–76, row 135 columns 77–79, row 135 columns 80–82, row 135 columns 83–86, row 135 columns
87–90), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
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

theorem rows225C_875 : rowsJ 135 136 0 60 ≤ 249450951634061 := by decide +kernel

theorem rows225C_876 : rowsJ 135 136 60 69 ≤ 4495675906165 := by decide +kernel

theorem rows225C_877 : rowsJ 135 136 69 74 ≤ 2397932624274 := by decide +kernel

theorem rows225C_878 : rowsJ 135 136 74 77 ≤ 0 := by decide +kernel

theorem rows225C_879 : rowsJ 135 136 77 80 ≤ 0 := by decide +kernel

theorem rows225C_880 : rowsJ 135 136 80 83 ≤ 0 := by decide +kernel

theorem rows225C_881 : rowsJ 135 136 83 87 ≤ 0 := by decide +kernel

theorem rows225C_882 : rowsJ 135 136 87 91 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_875
#print axioms SieveCert.rows225C_882
