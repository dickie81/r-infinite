/-
# Round 631: the certificate at `L = 2285/1000`, parts 68–76 of 252

File 8 of 28: the parts `rows2285U_68` … `rows2285U_76` of `SieveCert2285U.lean`'s certificate on
`SieveGrid2285U.grid2285U` (9 parts, 56719 depth-4 tests: row 61 columns 59–249, row 62 columns 0–50, row 62 columns
51–57, row 62 columns 58–249, row 63 columns 0–50, row 63 columns 51–57, row 63 columns 58–62, row 63 columns
63–249, row 64 columns 0–50), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide +kernel`, one at
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

theorem rows2285U_68 : rowsJ 61 62 59 250 ≤ 38835059033314 := by decide +kernel

theorem rows2285U_69 : rowsJ 62 63 0 51 ≤ 952730047104501 := by decide +kernel

theorem rows2285U_70 : rowsJ 62 63 51 58 ≤ 23381821052851 := by decide +kernel

theorem rows2285U_71 : rowsJ 62 63 58 250 ≤ 55562938228316 := by decide +kernel

theorem rows2285U_72 : rowsJ 63 64 0 51 ≤ 907400306603182 := by decide +kernel

theorem rows2285U_73 : rowsJ 63 64 51 58 ≤ 23148260203293 := by decide +kernel

theorem rows2285U_74 : rowsJ 63 64 58 63 ≤ 50725644807492 := by decide +kernel

theorem rows2285U_75 : rowsJ 63 64 63 250 ≤ 8876610360104 := by decide +kernel

theorem rows2285U_76 : rowsJ 64 65 0 51 ≤ 861463465881398 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2285U_68
#print axioms SieveCert.rows2285U_76
