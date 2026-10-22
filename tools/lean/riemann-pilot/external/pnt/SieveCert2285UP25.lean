/-
# Round 631: the certificate at `L = 2285/1000`, parts 213–221 of 252

File 25 of 28: the parts `rows2285U_213` … `rows2285U_221` of `SieveCert2285U.lean`'s certificate on
`SieveGrid2285U.grid2285U` (9 parts, 55788 depth-4 tests: row 101 columns 41–249, row 102 columns 0–40, row 102
columns 41–249, row 103 columns 0–40, row 103 columns 41–249, row 104 columns 0–40, row 104 columns 41–249, row 105
columns 0–39, row 105 columns 40–249), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide
+kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid2285U.lean`.
-/
import SieveGrid2285U

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid2285U

theorem rows2285U_213 : rowsJ 101 102 41 250 ≤ 1683101021737190 := by decide +kernel

theorem rows2285U_214 : rowsJ 102 103 0 41 ≤ 229246791618926 := by decide +kernel

theorem rows2285U_215 : rowsJ 102 103 41 250 ≤ 1944517051811636 := by decide +kernel

theorem rows2285U_216 : rowsJ 103 104 0 41 ≤ 243042507609415 := by decide +kernel

theorem rows2285U_217 : rowsJ 103 104 41 250 ≤ 2201814310575874 := by decide +kernel

theorem rows2285U_218 : rowsJ 104 105 0 41 ≤ 253527214283706 := by decide +kernel

theorem rows2285U_219 : rowsJ 104 105 41 250 ≤ 2454447669349697 := by decide +kernel

theorem rows2285U_220 : rowsJ 105 106 0 40 ≤ 243416768998015 := by decide +kernel

theorem rows2285U_221 : rowsJ 105 106 40 250 ≤ 2703821141206858 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2285U_213
#print axioms SieveCert.rows2285U_221
