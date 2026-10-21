/-
# Round 625: the certificate at `L = 9/4`, parts 89–97 of 1374

File 11 of 167: the parts `rows225C_89` … `rows225C_97` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (9 parts, 59310 depth-4 tests: row 59 columns 35–43, row 59 columns 44–49, row 59 columns
50–54, row 59 columns 55–58, row 59 columns 59–399, row 60 columns 0–34, row 60 columns 35–43, row 60 columns 44–49,
row 60 columns 50–54), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows225C_89 : rowsJ 59 60 35 44 ≤ 235540567655595 := by decide +kernel

theorem rows225C_90 : rowsJ 59 60 44 50 ≤ 97984537677189 := by decide +kernel

theorem rows225C_91 : rowsJ 59 60 50 55 ≤ 83520647770692 := by decide +kernel

theorem rows225C_92 : rowsJ 59 60 55 59 ≤ 87903070277988 := by decide +kernel

theorem rows225C_93 : rowsJ 59 60 59 400 ≤ 26326415293728 := by decide +kernel

theorem rows225C_94 : rowsJ 60 61 0 35 ≤ 877809906635799 := by decide +kernel

theorem rows225C_95 : rowsJ 60 61 35 44 ≤ 219779940180024 := by decide +kernel

theorem rows225C_96 : rowsJ 60 61 44 50 ≤ 91916430090138 := by decide +kernel

theorem rows225C_97 : rowsJ 60 61 50 55 ≤ 81872170549539 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_89
#print axioms SieveCert.rows225C_97
