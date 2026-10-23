/-
# Round 625: the certificate at `L = 9/4`, parts 370–377 of 1374

File 46 of 167: the parts `rows225C_370` … `rows225C_377` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (8 parts, 58635 depth-4 tests: row 96 columns 88–91, row 96 columns 92–94, row 96 columns
95–399, row 97 columns 0–34, row 97 columns 35–43, row 97 columns 44–50, row 97 columns 51–61, row 97 columns
62–81), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
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

theorem rows225C_370 : rowsJ 96 97 88 92 ≤ 7183212514302 := by decide +kernel

theorem rows225C_371 : rowsJ 96 97 92 95 ≤ 5552393872414 := by decide +kernel

theorem rows225C_372 : rowsJ 96 97 95 400 ≤ 5362727751228 := by decide +kernel

theorem rows225C_373 : rowsJ 97 98 0 35 ≤ 131513861138747 := by decide +kernel

theorem rows225C_374 : rowsJ 97 98 35 44 ≤ 101017666776009 := by decide +kernel

theorem rows225C_375 : rowsJ 97 98 44 51 ≤ 188793010875567 := by decide +kernel

theorem rows225C_376 : rowsJ 97 98 51 62 ≤ 237103604730235 := by decide +kernel

theorem rows225C_377 : rowsJ 97 98 62 82 ≤ 204610452712590 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_370
#print axioms SieveCert.rows225C_377
