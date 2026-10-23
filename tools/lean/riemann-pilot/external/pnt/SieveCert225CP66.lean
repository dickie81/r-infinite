/-
# Round 625: the certificate at `L = 9/4`, parts 534–540 of 1374

File 66 of 167: the parts `rows225C_534` … `rows225C_540` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (7 parts, 52809 depth-4 tests: row 110 columns 0–34, row 110 columns 35–44, row 110 columns
45–71, row 110 columns 72–80, row 110 columns 81–84, row 110 columns 85–87, row 110 columns 88–90), each a sum of
costs (`rows` or `rowsJ`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid225C.lean`.
-/
import SieveGrid225C

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid225C

theorem rows225C_534 : rowsJ 110 111 0 35 ≤ 62452499628542 := by decide +kernel

theorem rows225C_535 : rowsJ 110 111 35 45 ≤ 206493459479020 := by decide +kernel

theorem rows225C_536 : rowsJ 110 111 45 72 ≤ 297625441120098 := by decide +kernel

theorem rows225C_537 : rowsJ 110 111 72 81 ≤ 9005477691195 := by decide +kernel

theorem rows225C_538 : rowsJ 110 111 81 85 ≤ 14462852218 := by decide +kernel

theorem rows225C_539 : rowsJ 110 111 85 88 ≤ 466136678586 := by decide +kernel

theorem rows225C_540 : rowsJ 110 111 88 91 ≤ 1481741129300 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_534
#print axioms SieveCert.rows225C_540
