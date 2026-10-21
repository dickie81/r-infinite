/-
# Round 625: the certificate at `L = 9/4`, parts 132–139 of 1374

File 16 of 167: the parts `rows225C_132` … `rows225C_139` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (8 parts, 56493 depth-4 tests: row 65 columns 63–399, row 66 columns 0–34, row 66 columns
35–43, row 66 columns 44–49, row 66 columns 50–54, row 66 columns 55–58, row 66 columns 59–62, row 66 columns
63–399), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
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

theorem rows225C_132 : rowsJ 65 66 63 400 ≤ 112163286322880 := by decide +kernel

theorem rows225C_133 : rowsJ 66 67 0 35 ≤ 747507370613102 := by decide +kernel

theorem rows225C_134 : rowsJ 66 67 35 44 ≤ 137913445397798 := by decide +kernel

theorem rows225C_135 : rowsJ 66 67 44 50 ≤ 65970926131015 := by decide +kernel

theorem rows225C_136 : rowsJ 66 67 50 55 ≤ 80966441229551 := by decide +kernel

theorem rows225C_137 : rowsJ 66 67 55 59 ≤ 100130770160395 := by decide +kernel

theorem rows225C_138 : rowsJ 66 67 59 63 ≤ 140510705020482 := by decide +kernel

theorem rows225C_139 : rowsJ 66 67 63 400 ≤ 145739300498576 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_132
#print axioms SieveCert.rows225C_139
