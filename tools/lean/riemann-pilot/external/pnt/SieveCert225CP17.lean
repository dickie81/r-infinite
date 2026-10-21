/-
# Round 625: the certificate at `L = 9/4`, parts 140–148 of 1374

File 17 of 167: the parts `rows225C_140` … `rows225C_148` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (9 parts, 59885 depth-4 tests: row 67 columns 0–34, row 67 columns 35–43, row 67 columns
44–49, row 67 columns 50–54, row 67 columns 55–58, row 67 columns 59–62, row 67 columns 63–66, row 67 columns
67–399, row 68 columns 0–34), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide +kernel`, one at
a time (`Elab.async false`).

The file imports `SieveGrid225C.lean`.
-/
import SieveGrid225C

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid225C

theorem rows225C_140 : rowsJ 67 68 0 35 ≤ 724894606982254 := by decide +kernel

theorem rows225C_141 : rowsJ 67 68 35 44 ≤ 126452340845584 := by decide +kernel

theorem rows225C_142 : rowsJ 67 68 44 50 ≤ 63425273988175 := by decide +kernel

theorem rows225C_143 : rowsJ 67 68 50 55 ≤ 82320932195361 := by decide +kernel

theorem rows225C_144 : rowsJ 67 68 55 59 ≤ 103305322428865 := by decide +kernel

theorem rows225C_145 : rowsJ 67 68 59 63 ≤ 143174390999102 := by decide +kernel

theorem rows225C_146 : rowsJ 67 68 63 67 ≤ 143201494137660 := by decide +kernel

theorem rows225C_147 : rowsJ 67 68 67 400 ≤ 34204755070085 := by decide +kernel

theorem rows225C_148 : rowsJ 68 69 0 35 ≤ 702138388708713 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_140
#print axioms SieveCert.rows225C_148
