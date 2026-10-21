/-
# Round 625: the certificate at `L = 9/4`, parts 115–123 of 1374

File 14 of 167: the parts `rows225C_115` … `rows225C_123` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (9 parts, 59650 depth-4 tests: row 63 columns 50–54, row 63 columns 55–58, row 63 columns
59–62, row 63 columns 63–399, row 64 columns 0–34, row 64 columns 35–43, row 64 columns 44–49, row 64 columns 50–54,
row 64 columns 55–58), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows225C_115 : rowsJ 63 64 50 55 ≤ 79395331815589 := by decide +kernel

theorem rows225C_116 : rowsJ 63 64 55 59 ≤ 92799466116566 := by decide +kernel

theorem rows225C_117 : rowsJ 63 64 59 63 ≤ 130026539939657 := by decide +kernel

theorem rows225C_118 : rowsJ 63 64 63 400 ≤ 39280484208546 := by decide +kernel

theorem rows225C_119 : rowsJ 64 65 0 35 ≤ 792071171993420 := by decide +kernel

theorem rows225C_120 : rowsJ 64 65 35 44 ≤ 162764345407282 := by decide +kernel

theorem rows225C_121 : rowsJ 64 65 44 50 ≤ 72605445489161 := by decide +kernel

theorem rows225C_122 : rowsJ 64 65 50 55 ≤ 79509091528573 := by decide +kernel

theorem rows225C_123 : rowsJ 64 65 55 59 ≤ 94885044616621 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_115
#print axioms SieveCert.rows225C_123
