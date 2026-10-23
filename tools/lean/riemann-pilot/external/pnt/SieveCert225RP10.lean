/-
# Round 705: the refined certificate at `L = 9/4` with `n = 200`, parts 39–42 of 117

File 10 of 27: the parts `rows225R_39` … `rows225R_42` of `SieveCert225R.lean`'s certificate on
`SieveGrid225R.grid225R` (4 parts, 27441 tests: row 54 columns 0–45, row 54 columns 46–199, row 55 columns 0–45, row
55 columns 46–199), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at
a time (`Elab.async false`).

The file imports `SieveGrid225R.lean`.
-/
import SieveGrid225R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid225R

theorem rows225R_39 : rowsJ2 54 55 0 46 ≤ 1656981103973698 := by decide +kernel

theorem rows225R_40 : rowsJ2 54 55 46 200 ≤ 36542950867983 := by decide +kernel

theorem rows225R_41 : rowsJ2 55 56 0 46 ≤ 1553118352598444 := by decide +kernel

theorem rows225R_42 : rowsJ2 55 56 46 200 ≤ 46095947495958 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225R_39
#print axioms SieveCert.rows225R_42
