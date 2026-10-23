/-
# Round 631: the certificate at `L = 2285/1000`, parts 119–126 of 252

File 14 of 28: the parts `rows2285U_119` … `rows2285U_126` of `SieveCert2285U.lean`'s certificate on
`SieveGrid2285U.grid2285U` (8 parts, 54454 depth-4 tests: row 74 columns 0–48, row 74 columns 49–55, row 74 columns
56–62, row 74 columns 63–71, row 74 columns 72–249, row 75 columns 0–48, row 75 columns 49–55, row 75 columns
56–62), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
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

theorem rows2285U_119 : rowsJ 74 75 0 49 ≤ 512861657129677 := by decide +kernel

theorem rows2285U_120 : rowsJ 74 75 49 56 ≤ 6717845633200 := by decide +kernel

theorem rows2285U_121 : rowsJ 74 75 56 63 ≤ 5712400161593 := by decide +kernel

theorem rows2285U_122 : rowsJ 74 75 63 72 ≤ 13380735059881 := by decide +kernel

theorem rows2285U_123 : rowsJ 74 75 72 250 ≤ 268835564700802 := by decide +kernel

theorem rows2285U_124 : rowsJ 75 76 0 49 ≤ 485778600017987 := by decide +kernel

theorem rows2285U_125 : rowsJ 75 76 49 56 ≤ 5620254521678 := by decide +kernel

theorem rows2285U_126 : rowsJ 75 76 56 63 ≤ 3327135345898 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2285U_119
#print axioms SieveCert.rows2285U_126
