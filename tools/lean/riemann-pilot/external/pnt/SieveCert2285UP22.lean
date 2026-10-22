/-
# Round 631: the certificate at `L = 2285/1000`, parts 184–192 of 252

File 22 of 28: the parts `rows2285U_184` … `rows2285U_192` of `SieveCert2285U.lean`'s certificate on
`SieveGrid2285U.grid2285U` (9 parts, 57791 depth-4 tests: row 91 columns 0–43, row 91 columns 44–52, row 91 columns
53–249, row 92 columns 0–43, row 92 columns 44–52, row 92 columns 53–249, row 93 columns 0–43, row 93 columns 44–52,
row 93 columns 53–249), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide +kernel`, one at a
time (`Elab.async false`).

The file imports `SieveGrid2285U.lean`.
-/
import SieveGrid2285U

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid2285U

theorem rows2285U_184 : rowsJ 91 92 0 44 ≤ 231435808155711 := by decide +kernel

theorem rows2285U_185 : rowsJ 91 92 44 53 ≤ 49125752021468 := by decide +kernel

theorem rows2285U_186 : rowsJ 91 92 53 250 ≤ 0 := by decide +kernel

theorem rows2285U_187 : rowsJ 92 93 0 44 ≤ 228358828609680 := by decide +kernel

theorem rows2285U_188 : rowsJ 92 93 44 53 ≤ 57699461921536 := by decide +kernel

theorem rows2285U_189 : rowsJ 92 93 53 250 ≤ 0 := by decide +kernel

theorem rows2285U_190 : rowsJ 93 94 0 44 ≤ 230404529270230 := by decide +kernel

theorem rows2285U_191 : rowsJ 93 94 44 53 ≤ 65599823721270 := by decide +kernel

theorem rows2285U_192 : rowsJ 93 94 53 250 ≤ 744159940799 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2285U_184
#print axioms SieveCert.rows2285U_192
