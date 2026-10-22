/-
# Round 631: the certificate at `L = 2285/1000`, parts 150–157 of 252

File 18 of 28: the parts `rows2285U_150` … `rows2285U_157` of `SieveCert2285U.lean`'s certificate on
`SieveGrid2285U.grid2285U` (8 parts, 54082 depth-4 tests: row 81 columns 54–61, row 81 columns 62–249, row 82
columns 0–46, row 82 columns 47–53, row 82 columns 54–62, row 82 columns 63–249, row 83 columns 0–46, row 83 columns
47–53), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
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

theorem rows2285U_150 : rowsJ 81 82 54 62 ≤ 0 := by decide +kernel

theorem rows2285U_151 : rowsJ 81 82 62 250 ≤ 251767404319816 := by decide +kernel

theorem rows2285U_152 : rowsJ 82 83 0 47 ≤ 318490505628178 := by decide +kernel

theorem rows2285U_153 : rowsJ 82 83 47 54 ≤ 0 := by decide +kernel

theorem rows2285U_154 : rowsJ 82 83 54 63 ≤ 0 := by decide +kernel

theorem rows2285U_155 : rowsJ 82 83 63 250 ≤ 2722336624377 := by decide +kernel

theorem rows2285U_156 : rowsJ 83 84 0 47 ≤ 304145355421189 := by decide +kernel

theorem rows2285U_157 : rowsJ 83 84 47 54 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2285U_150
#print axioms SieveCert.rows2285U_157
