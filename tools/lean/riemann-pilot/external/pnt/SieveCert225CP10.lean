/-
# Round 625: the certificate at `L = 9/4`, parts 81–88 of 1374

File 10 of 167: the parts `rows225C_81` … `rows225C_88` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (8 parts, 55880 depth-4 tests: row 57 columns 50–54, row 57 columns 55–399, row 58 columns
0–34, row 58 columns 35–43, row 58 columns 44–49, row 58 columns 50–54, row 58 columns 55–399, row 59 columns 0–34),
each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid225C.lean`.
-/
import SieveGrid225C

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid225C

theorem rows225C_81 : rowsJ 57 58 50 55 ≤ 88197903257236 := by decide +kernel

theorem rows225C_82 : rowsJ 57 58 55 400 ≤ 63453978832900 := by decide +kernel

theorem rows225C_83 : rowsJ 58 59 0 35 ≤ 918553389804043 := by decide +kernel

theorem rows225C_84 : rowsJ 58 59 35 44 ≤ 251838333219717 := by decide +kernel

theorem rows225C_85 : rowsJ 58 59 44 50 ≤ 104541397397005 := by decide +kernel

theorem rows225C_86 : rowsJ 58 59 50 55 ≤ 85682562714490 := by decide +kernel

theorem rows225C_87 : rowsJ 58 59 55 400 ≤ 87512808530124 := by decide +kernel

theorem rows225C_88 : rowsJ 59 60 0 35 ≤ 898341020670268 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_81
#print axioms SieveCert.rows225C_88
