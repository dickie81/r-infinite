/-
# Round 625: the certificate at `L = 9/4`, parts 661–668 of 1374

File 82 of 167: the parts `rows225C_661` … `rows225C_668` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (8 parts, 54703 depth-4 tests: row 118 columns 101–104, row 118 columns 105–108, row 118
columns 109–113, row 118 columns 114–399, row 119 columns 0–34, row 119 columns 35–57, row 119 columns 58–75, row
119 columns 76–79), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows225C_661 : rowsJ 118 119 101 105 ≤ 2710141722597 := by decide +kernel

theorem rows225C_662 : rowsJ 118 119 105 109 ≤ 7219705980934 := by decide +kernel

theorem rows225C_663 : rowsJ 118 119 109 114 ≤ 19017792056689 := by decide +kernel

theorem rows225C_664 : rowsJ 118 119 114 400 ≤ 315559514430644 := by decide +kernel

theorem rows225C_665 : rowsJ 119 120 0 35 ≤ 92974514538307 := by decide +kernel

theorem rows225C_666 : rowsJ 119 120 35 58 ≤ 308821668807145 := by decide +kernel

theorem rows225C_667 : rowsJ 119 120 58 76 ≤ 29029680092400 := by decide +kernel

theorem rows225C_668 : rowsJ 119 120 76 80 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_661
#print axioms SieveCert.rows225C_668
