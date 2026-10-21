/-
# Round 625: the certificate at `L = 9/4`, parts 56–63 of 1374

File 7 of 167: the parts `rows225C_56` … `rows225C_63` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (8 parts, 53955 depth-4 tests: row 52 columns 0–34, row 52 columns 35–43, row 52 columns
44–49, row 52 columns 50–399, row 53 columns 0–34, row 53 columns 35–43, row 53 columns 44–49, row 53 columns
50–399), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
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

theorem rows225C_56 : rowsJ 52 53 0 35 ≤ 1029843933714858 := by decide +kernel

theorem rows225C_57 : rowsJ 52 53 35 44 ≤ 361520787776023 := by decide +kernel

theorem rows225C_58 : rowsJ 52 53 44 50 ≤ 154140311257771 := by decide +kernel

theorem rows225C_59 : rowsJ 52 53 50 400 ≤ 64733151425436 := by decide +kernel

theorem rows225C_60 : rowsJ 53 54 0 35 ≤ 1012403628925222 := by decide +kernel

theorem rows225C_61 : rowsJ 53 54 35 44 ≤ 342018679827533 := by decide +kernel

theorem rows225C_62 : rowsJ 53 54 44 50 ≤ 144655628968104 := by decide +kernel

theorem rows225C_63 : rowsJ 53 54 50 400 ≤ 81963204008131 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_56
#print axioms SieveCert.rows225C_63
