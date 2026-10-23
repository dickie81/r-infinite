/-
# Round 631: the certificate at `L = 2285/1000`, parts 176–183 of 252

File 21 of 28: the parts `rows2285U_176` … `rows2285U_183` of `SieveCert2285U.lean`'s certificate on
`SieveGrid2285U.grid2285U` (8 parts, 56820 depth-4 tests: row 88 columns 45–52, row 88 columns 53–249, row 89
columns 0–44, row 89 columns 45–52, row 89 columns 53–249, row 90 columns 0–44, row 90 columns 45–53, row 90 columns
54–249), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
false`).

The file imports `SieveGrid2285U.lean`.
-/
import SieveGrid2285U

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid2285U

theorem rows2285U_176 : rowsJ 88 89 45 53 ≤ 15013998091247 := by decide +kernel

theorem rows2285U_177 : rowsJ 88 89 53 250 ≤ 0 := by decide +kernel

theorem rows2285U_178 : rowsJ 89 90 0 45 ≤ 247487685965956 := by decide +kernel

theorem rows2285U_179 : rowsJ 89 90 45 53 ≤ 22451108565487 := by decide +kernel

theorem rows2285U_180 : rowsJ 89 90 53 250 ≤ 0 := by decide +kernel

theorem rows2285U_181 : rowsJ 90 91 0 45 ≤ 242266992461568 := by decide +kernel

theorem rows2285U_182 : rowsJ 90 91 45 54 ≤ 29918844063318 := by decide +kernel

theorem rows2285U_183 : rowsJ 90 91 54 250 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2285U_176
#print axioms SieveCert.rows2285U_183
