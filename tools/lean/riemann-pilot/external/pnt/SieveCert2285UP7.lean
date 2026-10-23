/-
# Round 631: the certificate at `L = 2285/1000`, parts 59–67 of 252

File 7 of 28: the parts `rows2285U_59` … `rows2285U_67` of `SieveCert2285U.lean`'s certificate on
`SieveGrid2285U.grid2285U` (9 parts, 57496 depth-4 tests: row 58 columns 51–249, row 59 columns 0–50, row 59 columns
51–58, row 59 columns 59–249, row 60 columns 0–50, row 60 columns 51–58, row 60 columns 59–249, row 61 columns 0–50,
row 61 columns 51–58), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows2285U_59 : rowsJ 58 59 51 250 ≤ 34562137318521 := by decide +kernel

theorem rows2285U_60 : rowsJ 59 60 0 51 ≤ 1111099969505650 := by decide +kernel

theorem rows2285U_61 : rowsJ 59 60 51 59 ≤ 33650180715636 := by decide +kernel

theorem rows2285U_62 : rowsJ 59 60 59 250 ≤ 11797799298248 := by decide +kernel

theorem rows2285U_63 : rowsJ 60 61 0 51 ≤ 1054014914161073 := by decide +kernel

theorem rows2285U_64 : rowsJ 60 61 51 59 ≤ 33310762918289 := by decide +kernel

theorem rows2285U_65 : rowsJ 60 61 59 250 ≤ 25801341933023 := by decide +kernel

theorem rows2285U_66 : rowsJ 61 62 0 51 ≤ 1003833041939827 := by decide +kernel

theorem rows2285U_67 : rowsJ 61 62 51 59 ≤ 32974936173944 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2285U_59
#print axioms SieveCert.rows2285U_67
