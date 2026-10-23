/-
# Round 631: the certificate at `L = 2285/1000`, parts 232–241 of 252

File 27 of 28: the parts `rows2285U_232` … `rows2285U_241` of `SieveCert2285U.lean`'s certificate on
`SieveGrid2285U.grid2285U` (10 parts, 56158 depth-4 tests: row 111 columns 0–38, row 111 columns 39–249, row 112
columns 0–38, row 112 columns 39–249, rows 113–113, rows 114–114, rows 115–115, rows 116–116, rows 117–117, rows
118–118), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
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

theorem rows2285U_232 : rowsJ 111 112 0 39 ≤ 307715838700046 := by decide +kernel

theorem rows2285U_233 : rowsJ 111 112 39 250 ≤ 4101835060418763 := by decide +kernel

theorem rows2285U_234 : rowsJ 112 113 0 39 ≤ 321526999365232 := by decide +kernel

theorem rows2285U_235 : rowsJ 112 113 39 250 ≤ 4227626878637211 := by decide +kernel

theorem rows2285U_236 : rows 113 114 ≤ 4586546078683815 := by decide +kernel

theorem rows2285U_237 : rows 114 115 ≤ 4608139838308413 := by decide +kernel

theorem rows2285U_238 : rows 115 116 ≤ 4645234746143384 := by decide +kernel

theorem rows2285U_239 : rows 116 117 ≤ 4678720607738531 := by decide +kernel

theorem rows2285U_240 : rows 117 118 ≤ 4701882066441873 := by decide +kernel

theorem rows2285U_241 : rows 118 119 ≤ 4734111908014256 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2285U_232
#print axioms SieveCert.rows2285U_241
