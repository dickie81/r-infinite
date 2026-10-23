/-
# Round 631: the certificate at `L = 2285/1000`, parts 50–58 of 252

File 6 of 28: the parts `rows2285U_50` … `rows2285U_58` of `SieveCert2285U.lean`'s certificate on
`SieveGrid2285U.grid2285U` (9 parts, 56614 depth-4 tests: row 54 columns 0–47, row 54 columns 48–249, row 55 columns
0–48, row 55 columns 49–249, row 56 columns 0–49, row 56 columns 50–249, row 57 columns 0–49, row 57 columns 50–249,
row 58 columns 0–50), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows2285U_50 : rowsJ 54 55 0 48 ≤ 1379271734938936 := by decide +kernel

theorem rows2285U_51 : rowsJ 54 55 48 250 ≤ 60087019277891 := by decide +kernel

theorem rows2285U_52 : rowsJ 55 56 0 49 ≤ 1335589515481622 := by decide +kernel

theorem rows2285U_53 : rowsJ 55 56 49 250 ≤ 38910395780766 := by decide +kernel

theorem rows2285U_54 : rowsJ 56 57 0 50 ≤ 1282436448635921 := by decide +kernel

theorem rows2285U_55 : rowsJ 56 57 50 250 ≤ 27952732416372 := by decide +kernel

theorem rows2285U_56 : rowsJ 57 58 0 50 ≤ 1224692921625862 := by decide +kernel

theorem rows2285U_57 : rowsJ 57 58 50 250 ≤ 30189874007928 := by decide +kernel

theorem rows2285U_58 : rowsJ 58 59 0 51 ≤ 1166760914862192 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2285U_50
#print axioms SieveCert.rows2285U_58
