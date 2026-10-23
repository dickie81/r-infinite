/-
# Round 625: the certificate at `L = 9/4`, parts 340–347 of 1374

File 42 of 167: the parts `rows225C_340` … `rows225C_347` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (8 parts, 58415 depth-4 tests: row 93 columns 35–43, row 93 columns 44–50, row 93 columns
51–58, row 93 columns 59–74, row 93 columns 75–86, row 93 columns 87–90, row 93 columns 91–399, row 94 columns
0–34), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
false`).

The file imports `SieveGrid225C.lean`.
-/
import SieveGrid225C

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid225C

theorem rows225C_340 : rowsJ 93 94 35 44 ≤ 75087446547198 := by decide +kernel

theorem rows225C_341 : rowsJ 93 94 44 51 ≤ 182432431196188 := by decide +kernel

theorem rows225C_342 : rowsJ 93 94 51 59 ≤ 204832232315326 := by decide +kernel

theorem rows225C_343 : rowsJ 93 94 59 75 ≤ 263247467688781 := by decide +kernel

theorem rows225C_344 : rowsJ 93 94 75 87 ≤ 83397364222053 := by decide +kernel

theorem rows225C_345 : rowsJ 93 94 87 91 ≤ 12773430432216 := by decide +kernel

theorem rows225C_346 : rowsJ 93 94 91 400 ≤ 7947923271540 := by decide +kernel

theorem rows225C_347 : rowsJ 94 95 0 35 ≤ 167510315478951 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_340
#print axioms SieveCert.rows225C_347
