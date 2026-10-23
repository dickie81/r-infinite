/-
# Round 625: the certificate at `L = 9/4`, parts 580–587 of 1374

File 72 of 167: the parts `rows225C_580` … `rows225C_587` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (8 parts, 56914 depth-4 tests: row 113 columns 81–84, row 113 columns 85–87, row 113
columns 88–90, row 113 columns 91–93, row 113 columns 94–96, row 113 columns 97–99, row 113 columns 100–102, row 113
columns 103–105), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows225C_580 : rowsJ 113 114 81 85 ≤ 14218306374 := by decide +kernel

theorem rows225C_581 : rowsJ 113 114 85 88 ≤ 456410898267 := by decide +kernel

theorem rows225C_582 : rowsJ 113 114 88 91 ≤ 761943095419 := by decide +kernel

theorem rows225C_583 : rowsJ 113 114 91 94 ≤ 440515427927 := by decide +kernel

theorem rows225C_584 : rowsJ 113 114 94 97 ≤ 198586085624 := by decide +kernel

theorem rows225C_585 : rowsJ 113 114 97 100 ≤ 52461031001 := by decide +kernel

theorem rows225C_586 : rowsJ 113 114 100 103 ≤ 275144710904 := by decide +kernel

theorem rows225C_587 : rowsJ 113 114 103 106 ≤ 1523767730170 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_580
#print axioms SieveCert.rows225C_587
