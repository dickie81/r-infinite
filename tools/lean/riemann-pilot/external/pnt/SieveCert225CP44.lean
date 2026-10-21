/-
# Round 625: the certificate at `L = 9/4`, parts 355–361 of 1374

File 44 of 167: the parts `rows225C_355` … `rows225C_361` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (7 parts, 53498 depth-4 tests: row 95 columns 0–34, row 95 columns 35–43, row 95 columns
44–50, row 95 columns 51–59, row 95 columns 60–80, row 95 columns 81–87, row 95 columns 88–91), each a sum of costs
(`rows` or `rowsJ`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid225C.lean`.
-/
import SieveGrid225C

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid225C

theorem rows225C_355 : rowsJ 95 96 0 35 ≤ 154590581888606 := by decide +kernel

theorem rows225C_356 : rowsJ 95 96 35 44 ≤ 87447358410299 := by decide +kernel

theorem rows225C_357 : rowsJ 95 96 44 51 ≤ 187406896833479 := by decide +kernel

theorem rows225C_358 : rowsJ 95 96 51 60 ≤ 214218028863151 := by decide +kernel

theorem rows225C_359 : rowsJ 95 96 60 81 ≤ 264407964643291 := by decide +kernel

theorem rows225C_360 : rowsJ 95 96 81 88 ≤ 27510957160155 := by decide +kernel

theorem rows225C_361 : rowsJ 95 96 88 92 ≤ 8639385719169 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_355
#print axioms SieveCert.rows225C_361
