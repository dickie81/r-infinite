/-
# Round 625: the certificate at `L = 9/4`, parts 324–331 of 1374

File 40 of 167: the parts `rows225C_324` … `rows225C_331` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (8 parts, 54505 depth-4 tests: row 91 columns 35–43, row 91 columns 44–49, row 91 columns
50–56, row 91 columns 57–67, row 91 columns 68–85, row 91 columns 86–90, row 91 columns 91–399, row 92 columns
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

theorem rows225C_324 : rowsJ 91 92 35 44 ≤ 63925214288409 := by decide +kernel

theorem rows225C_325 : rowsJ 91 92 44 50 ≤ 143749320531695 := by decide +kernel

theorem rows225C_326 : rowsJ 91 92 50 57 ≤ 196667807371899 := by decide +kernel

theorem rows225C_327 : rowsJ 91 92 57 68 ≤ 234528486619301 := by decide +kernel

theorem rows225C_328 : rowsJ 91 92 68 86 ≤ 194291973358236 := by decide +kernel

theorem rows225C_329 : rowsJ 91 92 86 91 ≤ 21561630607377 := by decide +kernel

theorem rows225C_330 : rowsJ 91 92 91 400 ≤ 3555535929725 := by decide +kernel

theorem rows225C_331 : rowsJ 92 93 0 35 ≤ 195863393846035 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_324
#print axioms SieveCert.rows225C_331
