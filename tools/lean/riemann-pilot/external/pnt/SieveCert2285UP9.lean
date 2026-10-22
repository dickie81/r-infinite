/-
# Round 631: the certificate at `L = 2285/1000`, parts 77–85 of 252

File 9 of 28: the parts `rows2285U_77` … `rows2285U_85` of `SieveCert2285U.lean`'s certificate on
`SieveGrid2285U.grid2285U` (9 parts, 58087 depth-4 tests: row 64 columns 51–57, row 64 columns 58–62, row 64 columns
63–249, row 65 columns 0–50, row 65 columns 51–57, row 65 columns 58–62, row 65 columns 63–249, row 66 columns 0–50,
row 66 columns 51–57), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide +kernel`, one at a time
(`Elab.async false`).

The file imports `SieveGrid2285U.lean`.
-/
import SieveGrid2285U

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid2285U

theorem rows2285U_77 : rowsJ 64 65 51 58 ≤ 22919901208135 := by decide +kernel

theorem rows2285U_78 : rowsJ 64 65 58 63 ≤ 44853958581960 := by decide +kernel

theorem rows2285U_79 : rowsJ 64 65 63 250 ≤ 14522503404954 := by decide +kernel

theorem rows2285U_80 : rowsJ 65 66 0 51 ≤ 821117767818482 := by decide +kernel

theorem rows2285U_81 : rowsJ 65 66 51 58 ≤ 22696615405927 := by decide +kernel

theorem rows2285U_82 : rowsJ 65 66 58 63 ≤ 39453402432501 := by decide +kernel

theorem rows2285U_83 : rowsJ 65 66 63 250 ≤ 17454517444955 := by decide +kernel

theorem rows2285U_84 : rowsJ 66 67 0 51 ≤ 779098394902564 := by decide +kernel

theorem rows2285U_85 : rowsJ 66 67 51 58 ≤ 22474501198161 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2285U_77
#print axioms SieveCert.rows2285U_85
