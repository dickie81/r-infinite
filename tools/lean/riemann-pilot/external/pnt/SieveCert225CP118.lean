/-
# Round 625: the certificate at `L = 9/4`, parts 960–967 of 1374

File 118 of 167: the parts `rows225C_960` … `rows225C_967` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (8 parts, 56420 depth-4 tests: row 142 columns 79–82, row 142 columns 83–86, row 142
columns 87–91, row 142 columns 92–97, row 142 columns 98–399, row 143 columns 0–60, row 143 columns 61–66, row 143
columns 67–70), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows225C_960 : rowsJ 142 143 79 83 ≤ 488511689075 := by decide +kernel

theorem rows225C_961 : rowsJ 142 143 83 87 ≤ 0 := by decide +kernel

theorem rows225C_962 : rowsJ 142 143 87 92 ≤ 0 := by decide +kernel

theorem rows225C_963 : rowsJ 142 143 92 98 ≤ 1020060256974 := by decide +kernel

theorem rows225C_964 : rowsJ 142 143 98 400 ≤ 812601418028489 := by decide +kernel

theorem rows225C_965 : rowsJ 143 144 0 61 ≤ 180728873098267 := by decide +kernel

theorem rows225C_966 : rowsJ 143 144 61 67 ≤ 8416800808313 := by decide +kernel

theorem rows225C_967 : rowsJ 143 144 67 71 ≤ 8509213347226 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_960
#print axioms SieveCert.rows225C_967
