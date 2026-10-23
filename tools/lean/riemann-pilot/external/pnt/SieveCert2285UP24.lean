/-
# Round 631: the certificate at `L = 2285/1000`, parts 203–212 of 252

File 24 of 28: the parts `rows2285U_203` … `rows2285U_212` of `SieveCert2285U.lean`'s certificate on
`SieveGrid2285U.grid2285U` (10 parts, 59971 depth-4 tests: row 97 columns 43–53, row 97 columns 54–249, row 98
columns 0–41, row 98 columns 42–52, row 98 columns 53–249, row 99 columns 0–41, row 99 columns 42–249, row 100
columns 0–41, row 100 columns 42–249, row 101 columns 0–40), each a sum of costs (`rows` or `rowsJ`) at most its
bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid2285U.lean`.
-/
import SieveGrid2285U

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid2285U

theorem rows2285U_203 : rowsJ 97 98 43 54 ≤ 100442328679062 := by decide +kernel

theorem rows2285U_204 : rowsJ 97 98 54 250 ≤ 436372962507672 := by decide +kernel

theorem rows2285U_205 : rowsJ 98 99 0 42 ≤ 214402370965187 := by decide +kernel

theorem rows2285U_206 : rowsJ 98 99 42 53 ≤ 119873667967471 := by decide +kernel

theorem rows2285U_207 : rowsJ 98 99 53 250 ≤ 722027616476264 := by decide +kernel

theorem rows2285U_208 : rowsJ 99 100 0 42 ≤ 224449369110940 := by decide +kernel

theorem rows2285U_209 : rowsJ 99 100 42 250 ≤ 1120058854632176 := by decide +kernel

theorem rows2285U_210 : rowsJ 100 101 0 42 ≤ 232055982726220 := by decide +kernel

theorem rows2285U_211 : rowsJ 100 101 42 250 ≤ 1392013830881192 := by decide +kernel

theorem rows2285U_212 : rowsJ 101 102 0 41 ≤ 219956673789885 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2285U_203
#print axioms SieveCert.rows2285U_212
