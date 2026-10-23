/-
# Round 631: the certificate at `L = 2285/1000`, parts 94–101 of 252

File 11 of 28: the parts `rows2285U_94` … `rows2285U_101` of `SieveCert2285U.lean`'s certificate on
`SieveGrid2285U.grid2285U` (8 parts, 59220 depth-4 tests: row 68 columns 57–62, row 68 columns 63–249, row 69
columns 0–49, row 69 columns 50–56, row 69 columns 57–62, row 69 columns 63–249, row 70 columns 0–49, row 70 columns
50–56), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
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

theorem rows2285U_94 : rowsJ 68 69 57 63 ≤ 28445002882681 := by decide +kernel

theorem rows2285U_95 : rowsJ 68 69 63 250 ≤ 14687545111109 := by decide +kernel

theorem rows2285U_96 : rowsJ 69 70 0 50 ≤ 671370396880025 := by decide +kernel

theorem rows2285U_97 : rowsJ 69 70 50 57 ≤ 15069593834851 := by decide +kernel

theorem rows2285U_98 : rowsJ 69 70 57 63 ≤ 22880133495528 := by decide +kernel

theorem rows2285U_99 : rowsJ 69 70 63 250 ≤ 13000636277763 := by decide +kernel

theorem rows2285U_100 : rowsJ 70 71 0 50 ≤ 636538364910951 := by decide +kernel

theorem rows2285U_101 : rowsJ 70 71 50 57 ≤ 14007582789044 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2285U_94
#print axioms SieveCert.rows2285U_101
