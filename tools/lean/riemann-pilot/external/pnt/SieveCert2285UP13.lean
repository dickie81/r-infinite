/-
# Round 631: the certificate at `L = 2285/1000`, parts 110–118 of 252

File 13 of 28: the parts `rows2285U_110` … `rows2285U_118` of `SieveCert2285U.lean`'s certificate on
`SieveGrid2285U.grid2285U` (9 parts, 55571 depth-4 tests: row 72 columns 50–55, row 72 columns 56–61, row 72 columns
62–69, row 72 columns 70–249, row 73 columns 0–48, row 73 columns 49–55, row 73 columns 56–62, row 73 columns 63–71,
row 73 columns 72–249), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide +kernel`, one at a
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

theorem rows2285U_110 : rowsJ 72 73 50 56 ≤ 8771312395220 := by decide +kernel

theorem rows2285U_111 : rowsJ 72 73 56 62 ≤ 11545868482230 := by decide +kernel

theorem rows2285U_112 : rowsJ 72 73 62 70 ≤ 5328044556966 := by decide +kernel

theorem rows2285U_113 : rowsJ 72 73 70 250 ≤ 18424556952137 := by decide +kernel

theorem rows2285U_114 : rowsJ 73 74 0 49 ≤ 544217047816902 := by decide +kernel

theorem rows2285U_115 : rowsJ 73 74 49 56 ≤ 8008840232852 := by decide +kernel

theorem rows2285U_116 : rowsJ 73 74 56 63 ≤ 8787424525420 := by decide +kernel

theorem rows2285U_117 : rowsJ 73 74 63 72 ≤ 13501914433764 := by decide +kernel

theorem rows2285U_118 : rowsJ 73 74 72 250 ≤ 21548614887985 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2285U_110
#print axioms SieveCert.rows2285U_118
