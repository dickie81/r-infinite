/-
# Round 631: the certificate at `L = 2285/1000`, parts 10–19 of 252

File 2 of 28: the parts `rows2285U_10` … `rows2285U_19` of `SieveCert2285U.lean`'s certificate on
`SieveGrid2285U.grid2285U` (10 parts, 52617 depth-4 tests: rows 33–33, rows 34–34, row 35 columns 0–34, row 35
columns 35–249, row 36 columns 0–34, row 36 columns 35–249, row 37 columns 0–34, row 37 columns 35–249, row 38
columns 0–34, row 38 columns 35–249), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide
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

theorem rows2285U_10 : rows 33 34 ≤ 1661828256033314 := by decide +kernel

theorem rows2285U_11 : rows 34 35 ≤ 1642607998689477 := by decide +kernel

theorem rows2285U_12 : rowsJ 35 36 0 35 ≤ 1565491439632208 := by decide +kernel

theorem rows2285U_13 : rowsJ 35 36 35 250 ≤ 86324305410024 := by decide +kernel

theorem rows2285U_14 : rowsJ 36 37 0 35 ≤ 1496197749695084 := by decide +kernel

theorem rows2285U_15 : rowsJ 36 37 35 250 ≤ 197692123875238 := by decide +kernel

theorem rows2285U_16 : rowsJ 37 38 0 35 ≤ 1434579002255837 := by decide +kernel

theorem rows2285U_17 : rowsJ 37 38 35 250 ≤ 314824829687675 := by decide +kernel

theorem rows2285U_18 : rowsJ 38 39 0 35 ≤ 1380608322403658 := by decide +kernel

theorem rows2285U_19 : rowsJ 38 39 35 250 ≤ 412575517532613 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2285U_10
#print axioms SieveCert.rows2285U_19
