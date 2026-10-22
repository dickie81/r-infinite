/-
# Round 631: the certificate at `L = 2285/1000`, parts 40–49 of 252

File 5 of 28: the parts `rows2285U_40` … `rows2285U_49` of `SieveCert2285U.lean`'s certificate on
`SieveGrid2285U.grid2285U` (10 parts, 50061 depth-4 tests: row 49 columns 0–36, row 49 columns 37–249, row 50
columns 0–37, row 50 columns 38–249, row 51 columns 0–38, row 51 columns 39–249, row 52 columns 0–39, row 52 columns
40–249, row 53 columns 0–42, row 53 columns 43–249), each a sum of costs (`rows` or `rowsJ`) at most its bound, by
`decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid2285U.lean`.
-/
import SieveGrid2285U

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid2285U

theorem rows2285U_40 : rowsJ 49 50 0 37 ≤ 1173819193223762 := by decide +kernel

theorem rows2285U_41 : rowsJ 49 50 37 250 ≤ 568894796515128 := by decide +kernel

theorem rows2285U_42 : rowsJ 50 51 0 38 ≤ 1203000443652763 := by decide +kernel

theorem rows2285U_43 : rowsJ 50 51 38 250 ≤ 487082372443473 := by decide +kernel

theorem rows2285U_44 : rowsJ 51 52 0 39 ≤ 1226514761954761 := by decide +kernel

theorem rows2285U_45 : rowsJ 51 52 39 250 ≤ 408830217090319 := by decide +kernel

theorem rows2285U_46 : rowsJ 52 53 0 40 ≤ 1237491225725025 := by decide +kernel

theorem rows2285U_47 : rowsJ 52 53 40 250 ≤ 334796603355788 := by decide +kernel

theorem rows2285U_48 : rowsJ 53 54 0 43 ≤ 1314478580954391 := by decide +kernel

theorem rows2285U_49 : rowsJ 53 54 43 250 ≤ 194665581031664 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2285U_40
#print axioms SieveCert.rows2285U_49
