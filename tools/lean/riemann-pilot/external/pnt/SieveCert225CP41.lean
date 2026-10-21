/-
# Round 625: the certificate at `L = 9/4`, parts 332–339 of 1374

File 41 of 167: the parts `rows225C_332` … `rows225C_339` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (8 parts, 56266 depth-4 tests: row 92 columns 35–43, row 92 columns 44–49, row 92 columns
50–56, row 92 columns 57–68, row 92 columns 69–85, row 92 columns 86–90, row 92 columns 91–399, row 93 columns
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

theorem rows225C_332 : rowsJ 92 93 35 44 ≤ 69348536289109 := by decide +kernel

theorem rows225C_333 : rowsJ 92 93 44 50 ≤ 148613890020344 := by decide +kernel

theorem rows225C_334 : rowsJ 92 93 50 57 ≤ 191933945233935 := by decide +kernel

theorem rows225C_335 : rowsJ 92 93 57 69 ≤ 242379320389429 := by decide +kernel

theorem rows225C_336 : rowsJ 92 93 69 86 ≤ 166604459894409 := by decide +kernel

theorem rows225C_337 : rowsJ 92 93 86 91 ≤ 19116932718663 := by decide +kernel

theorem rows225C_338 : rowsJ 92 93 91 400 ≤ 6118412887197 := by decide +kernel

theorem rows225C_339 : rowsJ 93 94 0 35 ≤ 181223773635464 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_332
#print axioms SieveCert.rows225C_339
