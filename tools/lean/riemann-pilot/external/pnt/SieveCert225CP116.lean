/-
# Round 625: the certificate at `L = 9/4`, parts 944–951 of 1374

File 116 of 167: the parts `rows225C_944` … `rows225C_951` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (8 parts, 56426 depth-4 tests: row 141 columns 0–60, row 141 columns 61–67, row 141 columns
68–71, row 141 columns 72–74, row 141 columns 75–77, row 141 columns 78–81, row 141 columns 82–85, row 141 columns
86–90), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
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

theorem rows225C_944 : rowsJ 141 142 0 61 ≤ 196549823916685 := by decide +kernel

theorem rows225C_945 : rowsJ 141 142 61 68 ≤ 8408577577451 := by decide +kernel

theorem rows225C_946 : rowsJ 141 142 68 72 ≤ 6976009181564 := by decide +kernel

theorem rows225C_947 : rowsJ 141 142 72 75 ≤ 4676329681608 := by decide +kernel

theorem rows225C_948 : rowsJ 141 142 75 78 ≤ 2541952857605 := by decide +kernel

theorem rows225C_949 : rowsJ 141 142 78 82 ≤ 556255176706 := by decide +kernel

theorem rows225C_950 : rowsJ 141 142 82 86 ≤ 0 := by decide +kernel

theorem rows225C_951 : rowsJ 141 142 86 91 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_944
#print axioms SieveCert.rows225C_951
