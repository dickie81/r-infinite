/-
# Round 625: the certificate at `L = 9/4`, parts 98–106 of 1374

File 12 of 167: the parts `rows225C_98` … `rows225C_106` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (9 parts, 59885 depth-4 tests: row 60 columns 55–58, row 60 columns 59–399, row 61 columns
0–34, row 61 columns 35–43, row 61 columns 44–49, row 61 columns 50–54, row 61 columns 55–58, row 61 columns 59–399,
row 62 columns 0–34), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows225C_98 : rowsJ 60 61 55 59 ≤ 88623434145025 := by decide +kernel

theorem rows225C_99 : rowsJ 60 61 59 400 ≤ 55628367177487 := by decide +kernel

theorem rows225C_100 : rowsJ 61 62 0 35 ≤ 856846540837077 := by decide +kernel

theorem rows225C_101 : rowsJ 61 62 35 44 ≤ 204656824626277 := by decide +kernel

theorem rows225C_102 : rowsJ 61 62 44 50 ≤ 86343504688644 := by decide +kernel

theorem rows225C_103 : rowsJ 61 62 50 55 ≤ 80583055205715 := by decide +kernel

theorem rows225C_104 : rowsJ 61 62 55 59 ≤ 89674625100442 := by decide +kernel

theorem rows225C_105 : rowsJ 61 62 59 400 ≤ 88782612610857 := by decide +kernel

theorem rows225C_106 : rowsJ 62 63 0 35 ≤ 835562582291431 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_98
#print axioms SieveCert.rows225C_106
