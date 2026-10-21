/-
# Round 625: the certificate at `L = 9/4`, parts 348–354 of 1374

File 43 of 167: the parts `rows225C_348` … `rows225C_354` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (7 parts, 53053 depth-4 tests: row 94 columns 35–43, row 94 columns 44–50, row 94 columns
51–59, row 94 columns 60–79, row 94 columns 80–87, row 94 columns 88–91, row 94 columns 92–399), each a sum of costs
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

theorem rows225C_348 : rowsJ 94 95 35 44 ≤ 81101050223845 := by decide +kernel

theorem rows225C_349 : rowsJ 94 95 44 51 ≤ 184961745078707 := by decide +kernel

theorem rows225C_350 : rowsJ 94 95 51 60 ≤ 220638025987785 := by decide +kernel

theorem rows225C_351 : rowsJ 94 95 60 80 ≤ 272234595079496 := by decide +kernel

theorem rows225C_352 : rowsJ 94 95 80 88 ≤ 37610553363040 := by decide +kernel

theorem rows225C_353 : rowsJ 94 95 88 92 ≤ 10203736014035 := by decide +kernel

theorem rows225C_354 : rowsJ 94 95 92 400 ≤ 6921637365303 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_348
#print axioms SieveCert.rows225C_354
