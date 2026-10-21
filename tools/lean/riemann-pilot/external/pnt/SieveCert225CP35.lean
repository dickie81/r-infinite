/-
# Round 625: the certificate at `L = 9/4`, parts 285–292 of 1374

File 35 of 167: the parts `rows225C_285` … `rows225C_292` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (8 parts, 58793 depth-4 tests: row 85 columns 55–61, row 85 columns 62–71, row 85 columns
72–399, row 86 columns 0–34, row 86 columns 35–43, row 86 columns 44–49, row 86 columns 50–55, row 86 columns
56–62), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
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

theorem rows225C_285 : rowsJ 85 86 55 62 ≤ 199627229289667 := by decide +kernel

theorem rows225C_286 : rowsJ 85 86 62 72 ≤ 223012089764200 := by decide +kernel

theorem rows225C_287 : rowsJ 85 86 72 400 ≤ 188113588390706 := by decide +kernel

theorem rows225C_288 : rowsJ 86 87 0 35 ≤ 301119301882776 := by decide +kernel

theorem rows225C_289 : rowsJ 86 87 35 44 ≤ 42760776680586 := by decide +kernel

theorem rows225C_290 : rowsJ 86 87 44 50 ≤ 112173417920583 := by decide +kernel

theorem rows225C_291 : rowsJ 86 87 50 56 ≤ 183625617520569 := by decide +kernel

theorem rows225C_292 : rowsJ 86 87 56 63 ≤ 189876012708658 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_285
#print axioms SieveCert.rows225C_292
