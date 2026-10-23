/-
# Round 625: the certificate at `L = 9/4`, parts 1370–1373 of 1374

File 167 of 167: the parts `rows225C_1370` … `rows225C_1373` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (4 parts, 0 depth-4 tests: rows 277–295, rows 296–312, rows 313–392, rows 393–399), each a
sum of costs (`rows` or `rowsJ`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid225C.lean`.
-/
import SieveGrid225C

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid225C

theorem rows225C_1370 : rows 277 296 ≤ 158332171736753373 := by decide +kernel

theorem rows225C_1371 : rows 296 313 ≤ 144429111799140829 := by decide +kernel

theorem rows225C_1372 : rows 313 393 ≤ 155631455086108719 := by decide +kernel

theorem rows225C_1373 : rows 393 400 ≤ 75414568941866684 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_1370
#print axioms SieveCert.rows225C_1373
