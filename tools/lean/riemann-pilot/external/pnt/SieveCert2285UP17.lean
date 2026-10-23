/-
# Round 631: the certificate at `L = 2285/1000`, parts 142–149 of 252

File 17 of 28: the parts `rows2285U_142` … `rows2285U_149` of `SieveCert2285U.lean`'s certificate on
`SieveGrid2285U.grid2285U` (8 parts, 55404 depth-4 tests: row 79 columns 55–62, row 79 columns 63–249, row 80
columns 0–47, row 80 columns 48–54, row 80 columns 55–62, row 80 columns 63–249, row 81 columns 0–46, row 81 columns
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

theorem rows2285U_142 : rowsJ 79 80 55 63 ≤ 46662486231 := by decide +kernel

theorem rows2285U_143 : rowsJ 79 80 63 250 ≤ 501306817850742 := by decide +kernel

theorem rows2285U_144 : rowsJ 80 81 0 48 ≤ 357409264990603 := by decide +kernel

theorem rows2285U_145 : rowsJ 80 81 48 55 ≤ 404531674165 := by decide +kernel

theorem rows2285U_146 : rowsJ 80 81 55 63 ≤ 0 := by decide +kernel

theorem rows2285U_147 : rowsJ 80 81 63 250 ≤ 255036003853987 := by decide +kernel

theorem rows2285U_148 : rowsJ 81 82 0 47 ≤ 338573036072476 := by decide +kernel

theorem rows2285U_149 : rowsJ 81 82 47 54 ≤ 133377755727 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2285U_142
#print axioms SieveCert.rows2285U_149
