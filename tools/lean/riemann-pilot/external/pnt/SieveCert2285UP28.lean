/-
# Round 631: the certificate at `L = 2285/1000`, parts 242–251 of 252

File 28 of 28: the parts `rows2285U_242` … `rows2285U_251` of `SieveCert2285U.lean`'s certificate on
`SieveGrid2285U.grid2285U` (10 parts, 47248 depth-4 tests: rows 119–119, rows 120–120, rows 121–121, rows 122–123,
rows 124–125, rows 126–128, rows 129–133, rows 134–168, rows 169–237, rows 238–249), each a sum of costs (`rows` or
`rowsJ`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid2285U.lean`.
-/
import SieveGrid2285U

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid2285U

theorem rows2285U_242 : rows 119 120 ≤ 4767733268305645 := by decide +kernel

theorem rows2285U_243 : rows 120 121 ≤ 4784657886309712 := by decide +kernel

theorem rows2285U_244 : rows 121 122 ≤ 4815399495189898 := by decide +kernel

theorem rows2285U_245 : rows 122 124 ≤ 9699541459483139 := by decide +kernel

theorem rows2285U_246 : rows 124 126 ≤ 9816393034370341 := by decide +kernel

theorem rows2285U_247 : rows 126 129 ≤ 14995423223489067 := by decide +kernel

theorem rows2285U_248 : rows 129 134 ≤ 26461339222297657 := by decide +kernel

theorem rows2285U_249 : rows 134 169 ≤ 353162748695670326 := by decide +kernel

theorem rows2285U_250 : rows 169 238 ≤ 364291736544275462 := by decide +kernel

theorem rows2285U_251 : rows 238 250 ≤ 170702245371894451 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2285U_242
#print axioms SieveCert.rows2285U_251
