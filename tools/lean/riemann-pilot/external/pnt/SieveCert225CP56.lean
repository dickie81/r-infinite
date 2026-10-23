/-
# Round 625: the certificate at `L = 9/4`, parts 454–461 of 1374

File 56 of 167: the parts `rows225C_454` … `rows225C_461` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (8 parts, 56690 depth-4 tests: row 104 columns 0–34, row 104 columns 35–43, row 104 columns
44–54, row 104 columns 55–78, row 104 columns 79–84, row 104 columns 85–87, row 104 columns 88–90, row 104 columns
91–92), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
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

theorem rows225C_454 : rowsJ 104 105 0 35 ≤ 77247476819035 := by decide +kernel

theorem rows225C_455 : rowsJ 104 105 35 44 ≤ 155923785427343 := by decide +kernel

theorem rows225C_456 : rowsJ 104 105 44 55 ≤ 241330011914701 := by decide +kernel

theorem rows225C_457 : rowsJ 104 105 55 79 ≤ 219425542079958 := by decide +kernel

theorem rows225C_458 : rowsJ 104 105 79 85 ≤ 6437515539836 := by decide +kernel

theorem rows225C_459 : rowsJ 104 105 85 88 ≤ 573726690381 := by decide +kernel

theorem rows225C_460 : rowsJ 104 105 88 91 ≤ 1815885594789 := by decide +kernel

theorem rows225C_461 : rowsJ 104 105 91 93 ≤ 2374732277207 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_454
#print axioms SieveCert.rows225C_461
