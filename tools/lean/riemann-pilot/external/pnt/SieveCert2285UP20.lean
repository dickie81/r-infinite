/-
# Round 631: the certificate at `L = 2285/1000`, parts 167–175 of 252

File 20 of 28: the parts `rows2285U_167` … `rows2285U_175` of `SieveCert2285U.lean`'s certificate on
`SieveGrid2285U.grid2285U` (9 parts, 55696 depth-4 tests: row 85 columns 63–249, row 86 columns 0–45, row 86 columns
46–53, row 86 columns 54–64, row 86 columns 65–249, row 87 columns 0–45, row 87 columns 46–53, row 87 columns
54–249, row 88 columns 0–44), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide +kernel`, one at
a time (`Elab.async false`).

The file imports `SieveGrid2285U.lean`.
-/
import SieveGrid2285U

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid2285U

theorem rows2285U_167 : rowsJ 85 86 63 250 ≤ 0 := by decide +kernel

theorem rows2285U_168 : rowsJ 86 87 0 46 ≤ 269365356112059 := by decide +kernel

theorem rows2285U_169 : rowsJ 86 87 46 54 ≤ 1472998128878 := by decide +kernel

theorem rows2285U_170 : rowsJ 86 87 54 65 ≤ 0 := by decide +kernel

theorem rows2285U_171 : rowsJ 86 87 65 250 ≤ 0 := by decide +kernel

theorem rows2285U_172 : rowsJ 87 88 0 46 ≤ 263857960915470 := by decide +kernel

theorem rows2285U_173 : rowsJ 87 88 46 54 ≤ 4750288976003 := by decide +kernel

theorem rows2285U_174 : rowsJ 87 88 54 250 ≤ 0 := by decide +kernel

theorem rows2285U_175 : rowsJ 88 89 0 45 ≤ 251054617320292 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2285U_167
#print axioms SieveCert.rows2285U_175
