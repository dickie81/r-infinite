/-
# Round 631: the certificate at `L = 2285/1000`, parts 30–39 of 252

File 4 of 28: the parts `rows2285U_30` … `rows2285U_39` of `SieveCert2285U.lean`'s certificate on
`SieveGrid2285U.grid2285U` (10 parts, 54734 depth-4 tests: row 44 columns 0–34, row 44 columns 35–249, row 45
columns 0–34, row 45 columns 35–249, row 46 columns 0–35, row 46 columns 36–249, row 47 columns 0–35, row 47 columns
36–249, row 48 columns 0–36, row 48 columns 37–249), each a sum of costs (`rows` or `rowsJ`) at most its bound, by
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

theorem rows2285U_30 : rowsJ 44 45 0 35 ≤ 1161927147154519 := by decide +kernel

theorem rows2285U_31 : rowsJ 44 45 35 250 ≤ 725716647317580 := by decide +kernel

theorem rows2285U_32 : rowsJ 45 46 0 35 ≤ 1135324198052954 := by decide +kernel

theorem rows2285U_33 : rowsJ 45 46 35 250 ≤ 740103081765457 := by decide +kernel

theorem rows2285U_34 : rowsJ 46 47 0 36 ≤ 1188519623248363 := by decide +kernel

theorem rows2285U_35 : rowsJ 46 47 36 250 ≤ 663257463969025 := by decide +kernel

theorem rows2285U_36 : rowsJ 47 48 0 36 ≤ 1161280788539234 := by decide +kernel

theorem rows2285U_37 : rowsJ 47 48 36 250 ≤ 662745220734252 := by decide +kernel

theorem rows2285U_38 : rowsJ 48 49 0 37 ≤ 1202130750695669 := by decide +kernel

theorem rows2285U_39 : rowsJ 48 49 37 250 ≤ 582706071415915 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2285U_30
#print axioms SieveCert.rows2285U_39
