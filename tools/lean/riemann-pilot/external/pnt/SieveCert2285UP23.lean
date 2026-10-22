/-
# Round 631: the certificate at `L = 2285/1000`, parts 193–202 of 252

File 23 of 28: the parts `rows2285U_193` … `rows2285U_202` of `SieveCert2285U.lean`'s certificate on
`SieveGrid2285U.grid2285U` (10 parts, 59833 depth-4 tests: row 94 columns 0–43, row 94 columns 44–53, row 94 columns
54–249, row 95 columns 0–42, row 95 columns 43–52, row 95 columns 53–249, row 96 columns 0–42, row 96 columns 43–53,
row 96 columns 54–249, row 97 columns 0–42), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide
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

theorem rows2285U_193 : rowsJ 94 95 0 44 ≤ 231482719800401 := by decide +kernel

theorem rows2285U_194 : rowsJ 94 95 44 54 ≤ 72046704373360 := by decide +kernel

theorem rows2285U_195 : rowsJ 94 95 54 250 ≤ 555214644845 := by decide +kernel

theorem rows2285U_196 : rowsJ 95 96 0 43 ≤ 219205751127115 := by decide +kernel

theorem rows2285U_197 : rowsJ 95 96 43 53 ≤ 93253445976377 := by decide +kernel

theorem rows2285U_198 : rowsJ 95 96 53 250 ≤ 3233488480341 := by decide +kernel

theorem rows2285U_199 : rowsJ 96 97 0 43 ≤ 222267231308801 := by decide +kernel

theorem rows2285U_200 : rowsJ 96 97 43 54 ≤ 98215324731829 := by decide +kernel

theorem rows2285U_201 : rowsJ 96 97 54 250 ≤ 148023664521913 := by decide +kernel

theorem rows2285U_202 : rowsJ 97 98 0 43 ≤ 230529466355960 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2285U_193
#print axioms SieveCert.rows2285U_202
