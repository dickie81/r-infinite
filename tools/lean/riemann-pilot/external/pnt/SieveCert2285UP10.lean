/-
# Round 631: the certificate at `L = 2285/1000`, parts 86–93 of 252

File 10 of 28: the parts `rows2285U_86` … `rows2285U_93` of `SieveCert2285U.lean`'s certificate on
`SieveGrid2285U.grid2285U` (8 parts, 54094 depth-4 tests: row 66 columns 58–63, row 66 columns 64–249, row 67
columns 0–50, row 67 columns 51–57, row 67 columns 58–63, row 67 columns 64–249, row 68 columns 0–49, row 68 columns
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

theorem rows2285U_86 : rowsJ 66 67 58 64 ≤ 38478730919795 := by decide +kernel

theorem rows2285U_87 : rowsJ 66 67 64 250 ≤ 12928124486624 := by decide +kernel

theorem rows2285U_88 : rowsJ 67 68 0 51 ≤ 742871111671025 := by decide +kernel

theorem rows2285U_89 : rowsJ 67 68 51 58 ≤ 22257460443617 := by decide +kernel

theorem rows2285U_90 : rowsJ 67 68 58 64 ≤ 31864597058619 := by decide +kernel

theorem rows2285U_91 : rowsJ 67 68 64 250 ≤ 12848917845797 := by decide +kernel

theorem rows2285U_92 : rowsJ 68 69 0 50 ≤ 704812446249394 := by decide +kernel

theorem rows2285U_93 : rowsJ 68 69 50 57 ≤ 15216330445137 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2285U_86
#print axioms SieveCert.rows2285U_93
