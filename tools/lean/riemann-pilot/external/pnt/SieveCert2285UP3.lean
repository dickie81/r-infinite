/-
# Round 631: the certificate at `L = 2285/1000`, parts 20–29 of 252

File 3 of 28: the parts `rows2285U_20` … `rows2285U_29` of `SieveCert2285U.lean`'s certificate on
`SieveGrid2285U.grid2285U` (10 parts, 55791 depth-4 tests: row 39 columns 0–34, row 39 columns 35–249, row 40
columns 0–34, row 40 columns 35–249, row 41 columns 0–34, row 41 columns 35–249, row 42 columns 0–34, row 42 columns
35–249, row 43 columns 0–34, row 43 columns 35–249), each a sum of costs (`rows` or `rowsJ`) at most its bound, by
`decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid2285U.lean`.
-/
import SieveGrid2285U

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid2285U

theorem rows2285U_20 : rowsJ 39 40 0 35 ≤ 1333176730623714 := by decide +kernel

theorem rows2285U_21 : rowsJ 39 40 35 250 ≤ 499182558938025 := by decide +kernel

theorem rows2285U_22 : rowsJ 40 41 0 35 ≤ 1293206618799457 := by decide +kernel

theorem rows2285U_23 : rowsJ 40 41 35 250 ≤ 566283592968959 := by decide +kernel

theorem rows2285U_24 : rowsJ 41 42 0 35 ≤ 1259171451614364 := by decide +kernel

theorem rows2285U_25 : rowsJ 41 42 35 250 ≤ 622177808497608 := by decide +kernel

theorem rows2285U_26 : rowsJ 42 43 0 35 ≤ 1223416903168198 := by decide +kernel

theorem rows2285U_27 : rowsJ 42 43 35 250 ≤ 667119225165624 := by decide +kernel

theorem rows2285U_28 : rowsJ 43 44 0 35 ≤ 1193701697572933 := by decide +kernel

theorem rows2285U_29 : rowsJ 43 44 35 250 ≤ 701544208856324 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2285U_20
#print axioms SieveCert.rows2285U_29
