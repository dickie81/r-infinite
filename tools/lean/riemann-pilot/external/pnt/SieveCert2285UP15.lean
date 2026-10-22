/-
# Round 631: the certificate at `L = 2285/1000`, parts 127–133 of 252

File 15 of 28: the parts `rows2285U_127` … `rows2285U_133` of `SieveCert2285U.lean`'s certificate on
`SieveGrid2285U.grid2285U` (7 parts, 52864 depth-4 tests: row 75 columns 63–249, row 76 columns 0–48, row 76 columns
49–55, row 76 columns 56–62, row 76 columns 63–249, row 77 columns 0–47, row 77 columns 48–54), each a sum of costs
(`rows` or `rowsJ`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid2285U.lean`.
-/
import SieveGrid2285U

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid2285U

theorem rows2285U_127 : rowsJ 75 76 63 250 ≤ 756318068243327 := by decide +kernel

theorem rows2285U_128 : rowsJ 76 77 0 49 ≤ 456338756423442 := by decide +kernel

theorem rows2285U_129 : rowsJ 76 77 49 56 ≤ 4222761533179 := by decide +kernel

theorem rows2285U_130 : rowsJ 76 77 56 63 ≤ 1629472841011 := by decide +kernel

theorem rows2285U_131 : rowsJ 76 77 63 250 ≤ 751432964757849 := by decide +kernel

theorem rows2285U_132 : rowsJ 77 78 0 48 ≤ 431197306424688 := by decide +kernel

theorem rows2285U_133 : rowsJ 77 78 48 55 ≤ 2683382029509 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2285U_127
#print axioms SieveCert.rows2285U_133
