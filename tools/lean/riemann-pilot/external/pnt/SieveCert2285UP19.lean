/-
# Round 631: the certificate at `L = 2285/1000`, parts 158–166 of 252

File 19 of 28: the parts `rows2285U_158` … `rows2285U_166` of `SieveCert2285U.lean`'s certificate on
`SieveGrid2285U.grid2285U` (9 parts, 58099 depth-4 tests: row 83 columns 54–62, row 83 columns 63–249, row 84
columns 0–46, row 84 columns 47–53, row 84 columns 54–63, row 84 columns 64–249, row 85 columns 0–45, row 85 columns
46–52, row 85 columns 53–62), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide +kernel`, one at
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

theorem rows2285U_158 : rowsJ 83 84 54 63 ≤ 0 := by decide +kernel

theorem rows2285U_159 : rowsJ 83 84 63 250 ≤ 0 := by decide +kernel

theorem rows2285U_160 : rowsJ 84 85 0 47 ≤ 288829793561832 := by decide +kernel

theorem rows2285U_161 : rowsJ 84 85 47 54 ≤ 0 := by decide +kernel

theorem rows2285U_162 : rowsJ 84 85 54 64 ≤ 0 := by decide +kernel

theorem rows2285U_163 : rowsJ 84 85 64 250 ≤ 0 := by decide +kernel

theorem rows2285U_164 : rowsJ 85 86 0 46 ≤ 280158371509662 := by decide +kernel

theorem rows2285U_165 : rowsJ 85 86 46 53 ≤ 0 := by decide +kernel

theorem rows2285U_166 : rowsJ 85 86 53 63 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2285U_158
#print axioms SieveCert.rows2285U_166
