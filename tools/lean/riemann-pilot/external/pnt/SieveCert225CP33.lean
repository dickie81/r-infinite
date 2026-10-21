/-
# Round 625: the certificate at `L = 9/4`, parts 269–276 of 1374

File 33 of 167: the parts `rows225C_269` … `rows225C_276` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (8 parts, 58575 depth-4 tests: row 83 columns 44–49, row 83 columns 50–54, row 83 columns
55–60, row 83 columns 61–68, row 83 columns 69–399, row 84 columns 0–34, row 84 columns 35–43, row 84 columns
44–49), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
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

theorem rows225C_269 : rowsJ 83 84 44 50 ≤ 95146767565093 := by decide +kernel

theorem rows225C_270 : rowsJ 83 84 50 55 ≤ 149094829104694 := by decide +kernel

theorem rows225C_271 : rowsJ 83 84 55 61 ≤ 181183074695781 := by decide +kernel

theorem rows225C_272 : rowsJ 83 84 61 69 ≤ 201735138800659 := by decide +kernel

theorem rows225C_273 : rowsJ 83 84 69 400 ≤ 250061127403800 := by decide +kernel

theorem rows225C_274 : rowsJ 84 85 0 35 ≤ 341460433968298 := by decide +kernel

theorem rows225C_275 : rowsJ 84 85 35 44 ≤ 38371319903793 := by decide +kernel

theorem rows225C_276 : rowsJ 84 85 44 50 ≤ 100632710322401 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_269
#print axioms SieveCert.rows225C_276
