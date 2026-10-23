/-
# Round 631: the certificate at `L = 2285/1000`, parts 102–109 of 252

File 12 of 28: the parts `rows2285U_102` … `rows2285U_109` of `SieveCert2285U.lean`'s certificate on
`SieveGrid2285U.grid2285U` (8 parts, 53951 depth-4 tests: row 70 columns 57–62, row 70 columns 63–249, row 71
columns 0–49, row 71 columns 50–55, row 71 columns 56–61, row 71 columns 62–69, row 71 columns 70–249, row 72
columns 0–49), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows2285U_102 : rowsJ 70 71 57 63 ≤ 17940919647811 := by decide +kernel

theorem rows2285U_103 : rowsJ 70 71 63 250 ≤ 12911970331598 := by decide +kernel

theorem rows2285U_104 : rowsJ 71 72 0 50 ≤ 606010768060873 := by decide +kernel

theorem rows2285U_105 : rowsJ 71 72 50 56 ≤ 9632950472184 := by decide +kernel

theorem rows2285U_106 : rowsJ 71 72 56 62 ≤ 15511407355355 := by decide +kernel

theorem rows2285U_107 : rowsJ 71 72 62 70 ≤ 8016299090681 := by decide +kernel

theorem rows2285U_108 : rowsJ 71 72 70 250 ≤ 9385335996123 := by decide +kernel

theorem rows2285U_109 : rowsJ 72 73 0 50 ≤ 572864581718350 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2285U_102
#print axioms SieveCert.rows2285U_109
