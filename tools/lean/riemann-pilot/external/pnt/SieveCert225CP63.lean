/-
# Round 625: the certificate at `L = 9/4`, parts 510–517 of 1374

File 63 of 167: the parts `rows225C_510` … `rows225C_517` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (8 parts, 55606 depth-4 tests: row 108 columns 81–84, row 108 columns 85–87, row 108
columns 88–90, row 108 columns 91–92, row 108 columns 93–95, row 108 columns 96–98, row 108 columns 99–101, row 108
columns 102–104), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows225C_510 : rowsJ 108 109 81 85 ≤ 105310712450 := by decide +kernel

theorem rows225C_511 : rowsJ 108 109 85 88 ≤ 471502686107 := by decide +kernel

theorem rows225C_512 : rowsJ 108 109 88 91 ≤ 1767420658158 := by decide +kernel

theorem rows225C_513 : rowsJ 108 109 91 93 ≤ 1369757956529 := by decide +kernel

theorem rows225C_514 : rowsJ 108 109 93 96 ≤ 1594895942810 := by decide +kernel

theorem rows225C_515 : rowsJ 108 109 96 99 ≤ 1103637647733 := by decide +kernel

theorem rows225C_516 : rowsJ 108 109 99 102 ≤ 696740973168 := by decide +kernel

theorem rows225C_517 : rowsJ 108 109 102 105 ≤ 523091480186 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_510
#print axioms SieveCert.rows225C_517
