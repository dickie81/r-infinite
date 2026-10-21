/-
# Round 625: the certificate at `L = 9/4`, parts 710–717 of 1374

File 88 of 167: the parts `rows225C_710` … `rows225C_717` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (8 parts, 56355 depth-4 tests: row 122 columns 69–75, row 122 columns 76–79, row 122
columns 80–82, row 122 columns 83–85, row 122 columns 86–88, row 122 columns 89–91, row 122 columns 92–94, row 122
columns 95–98), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows225C_710 : rowsJ 122 123 69 76 ≤ 0 := by decide +kernel

theorem rows225C_711 : rowsJ 122 123 76 80 ≤ 0 := by decide +kernel

theorem rows225C_712 : rowsJ 122 123 80 83 ≤ 0 := by decide +kernel

theorem rows225C_713 : rowsJ 122 123 83 86 ≤ 0 := by decide +kernel

theorem rows225C_714 : rowsJ 122 123 86 89 ≤ 0 := by decide +kernel

theorem rows225C_715 : rowsJ 122 123 89 92 ≤ 0 := by decide +kernel

theorem rows225C_716 : rowsJ 122 123 92 95 ≤ 0 := by decide +kernel

theorem rows225C_717 : rowsJ 122 123 95 99 ≤ 284749894030 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_710
#print axioms SieveCert.rows225C_717
