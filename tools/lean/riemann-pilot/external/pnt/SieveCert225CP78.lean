/-
# Round 625: the certificate at `L = 9/4`, parts 629–636 of 1374

File 78 of 167: the parts `rows225C_629` … `rows225C_636` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (8 parts, 54254 depth-4 tests: row 116 columns 96–98, row 116 columns 99–101, row 116
columns 102–105, row 116 columns 106–109, row 116 columns 110–113, row 116 columns 114–399, row 117 columns 0–34,
row 117 columns 35–50), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide +kernel`, one at a
time (`Elab.async false`).

The file imports `SieveGrid225C.lean`.
-/
import SieveGrid225C

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid225C

theorem rows225C_629 : rowsJ 116 117 96 99 ≤ 0 := by decide +kernel

theorem rows225C_630 : rowsJ 116 117 99 102 ≤ 409736364663 := by decide +kernel

theorem rows225C_631 : rowsJ 116 117 102 106 ≤ 2819048896620 := by decide +kernel

theorem rows225C_632 : rowsJ 116 117 106 110 ≤ 7407263626793 := by decide +kernel

theorem rows225C_633 : rowsJ 116 117 110 114 ≤ 14332229931615 := by decide +kernel

theorem rows225C_634 : rowsJ 116 117 114 400 ≤ 16822282181157 := by decide +kernel

theorem rows225C_635 : rowsJ 117 118 0 35 ≤ 80868812977651 := by decide +kernel

theorem rows225C_636 : rowsJ 117 118 35 51 ≤ 276458507698131 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_629
#print axioms SieveCert.rows225C_636
