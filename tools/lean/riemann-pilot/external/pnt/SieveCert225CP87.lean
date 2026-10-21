/-
# Round 625: the certificate at `L = 9/4`, parts 702–709 of 1374

File 87 of 167: the parts `rows225C_702` … `rows225C_709` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (8 parts, 56231 depth-4 tests: row 121 columns 92–94, row 121 columns 95–97, row 121
columns 98–101, row 121 columns 102–105, row 121 columns 106–110, row 121 columns 111–399, row 122 columns 0–34, row
122 columns 35–68), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows225C_702 : rowsJ 121 122 92 95 ≤ 0 := by decide +kernel

theorem rows225C_703 : rowsJ 121 122 95 98 ≤ 86008957662 := by decide +kernel

theorem rows225C_704 : rowsJ 121 122 98 102 ≤ 1421388451983 := by decide +kernel

theorem rows225C_705 : rowsJ 121 122 102 106 ≤ 4935194195705 := by decide +kernel

theorem rows225C_706 : rowsJ 121 122 106 111 ≤ 14748520345006 := by decide +kernel

theorem rows225C_707 : rowsJ 121 122 111 400 ≤ 711835126409850 := by decide +kernel

theorem rows225C_708 : rowsJ 122 123 0 35 ≤ 114227704443068 := by decide +kernel

theorem rows225C_709 : rowsJ 122 123 35 69 ≤ 276598804046844 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_702
#print axioms SieveCert.rows225C_709
