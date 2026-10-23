/-
# Round 631: the certificate at `L = 2285/1000`, parts 0–9 of 252

File 1 of 28: the parts `rows2285U_0` … `rows2285U_9` of `SieveCert2285U.lean`'s certificate on
`SieveGrid2285U.grid2285U` (10 parts, 58905 depth-4 tests: rows 0–18, rows 19–22, rows 23–24, rows 25–26, rows
27–27, rows 28–28, rows 29–29, rows 30–30, rows 31–31, rows 32–32), each a sum of costs (`rows` or `rowsJ`) at most
its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid2285U.lean`.
-/
import SieveGrid2285U

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid2285U

theorem rows2285U_0 : rows 0 19 ≤ 9880322320027400 := by decide +kernel

theorem rows2285U_1 : rows 19 23 ≤ 7207336374779032 := by decide +kernel

theorem rows2285U_2 : rows 23 25 ≤ 4094932995576876 := by decide +kernel

theorem rows2285U_3 : rows 25 27 ≤ 4121133396638523 := by decide +kernel

theorem rows2285U_4 : rows 27 28 ≤ 2010766765306789 := by decide +kernel

theorem rows2285U_5 : rows 28 29 ≤ 1956018101805529 := by decide +kernel

theorem rows2285U_6 : rows 29 30 ≤ 1891800118276708 := by decide +kernel

theorem rows2285U_7 : rows 30 31 ≤ 1824248922489747 := by decide +kernel

theorem rows2285U_8 : rows 31 32 ≤ 1759360990551195 := by decide +kernel

theorem rows2285U_9 : rows 32 33 ≤ 1703280661816607 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows2285U_0
#print axioms SieveCert.rows2285U_9
