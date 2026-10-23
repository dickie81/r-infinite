/-
# Round 625: the certificate at `L = 9/4`, parts 613–620 of 1374

File 76 of 167: the parts `rows225C_613` … `rows225C_620` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (8 parts, 52781 depth-4 tests: row 115 columns 93–95, row 115 columns 96–98, row 115
columns 99–101, row 115 columns 102–105, row 115 columns 106–109, row 115 columns 110–113, row 115 columns 114–399,
row 116 columns 0–34), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows225C_613 : rowsJ 115 116 93 96 ≤ 50993794552 := by decide +kernel

theorem rows225C_614 : rowsJ 115 116 96 99 ≤ 0 := by decide +kernel

theorem rows225C_615 : rowsJ 115 116 99 102 ≤ 281967340036 := by decide +kernel

theorem rows225C_616 : rowsJ 115 116 102 106 ≤ 2449930292414 := by decide +kernel

theorem rows225C_617 : rowsJ 115 116 106 110 ≤ 6798985378591 := by decide +kernel

theorem rows225C_618 : rowsJ 115 116 110 114 ≤ 13438849955510 := by decide +kernel

theorem rows225C_619 : rowsJ 115 116 114 400 ≤ 9983095435013 := by decide +kernel

theorem rows225C_620 : rowsJ 116 117 0 35 ≤ 75913716937550 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_613
#print axioms SieveCert.rows225C_620
