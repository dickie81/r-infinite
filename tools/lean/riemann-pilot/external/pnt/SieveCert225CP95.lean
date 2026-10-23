/-
# Round 625: the certificate at `L = 9/4`, parts 769–776 of 1374

File 95 of 167: the parts `rows225C_769` … `rows225C_776` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (8 parts, 54720 depth-4 tests: row 126 columns 82–84, row 126 columns 85–87, row 126
columns 88–90, row 126 columns 91–94, row 126 columns 95–98, row 126 columns 99–102, row 126 columns 103–107, row
126 columns 108–399), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows225C_769 : rowsJ 126 127 82 85 ≤ 0 := by decide +kernel

theorem rows225C_770 : rowsJ 126 127 85 88 ≤ 0 := by decide +kernel

theorem rows225C_771 : rowsJ 126 127 88 91 ≤ 0 := by decide +kernel

theorem rows225C_772 : rowsJ 126 127 91 95 ≤ 0 := by decide +kernel

theorem rows225C_773 : rowsJ 126 127 95 99 ≤ 576998937699 := by decide +kernel

theorem rows225C_774 : rowsJ 126 127 99 103 ≤ 3506841738977 := by decide +kernel

theorem rows225C_775 : rowsJ 126 127 103 108 ≤ 12281698969935 := by decide +kernel

theorem rows225C_776 : rowsJ 126 127 108 400 ≤ 1445365877699434 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_769
#print axioms SieveCert.rows225C_776
