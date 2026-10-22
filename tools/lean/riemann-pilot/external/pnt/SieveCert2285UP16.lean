/-
# Round 631: the certificate at `L = 2285/1000`, parts 134–141 of 252

File 16 of 28: the parts `rows2285U_134` … `rows2285U_141` of `SieveCert2285U.lean`'s certificate on
`SieveGrid2285U.grid2285U` (8 parts, 58902 depth-4 tests: row 77 columns 55–61, row 77 columns 62–249, row 78
columns 0–47, row 78 columns 48–54, row 78 columns 55–62, row 78 columns 63–249, row 79 columns 0–47, row 79 columns
48–54), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
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

theorem rows2285U_134 : rowsJ 77 78 55 62 ≤ 1039300510669 := by decide +kernel

theorem rows2285U_135 : rowsJ 77 78 62 250 ≤ 747972169806961 := by decide +kernel

theorem rows2285U_136 : rowsJ 78 79 0 48 ≤ 403884109220143 := by decide +kernel

theorem rows2285U_137 : rowsJ 78 79 48 55 ≤ 1722599816498 := by decide +kernel

theorem rows2285U_138 : rowsJ 78 79 55 63 ≤ 328572860242 := by decide +kernel

theorem rows2285U_139 : rowsJ 78 79 63 250 ≤ 504876149639500 := by decide +kernel

theorem rows2285U_140 : rowsJ 79 80 0 48 ≤ 381630369077124 := by decide +kernel

theorem rows2285U_141 : rowsJ 79 80 48 55 ≤ 1036435654063 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2285U_134
#print axioms SieveCert.rows2285U_141
