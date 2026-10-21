/-
# Round 625: the certificate at `L = 9/4`, parts 107–114 of 1374

File 13 of 167: the parts `rows225C_107` … `rows225C_114` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (8 parts, 58010 depth-4 tests: row 62 columns 35–43, row 62 columns 44–49, row 62 columns
50–54, row 62 columns 55–58, row 62 columns 59–399, row 63 columns 0–34, row 63 columns 35–43, row 63 columns
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

theorem rows225C_107 : rowsJ 62 63 35 44 ≤ 190066153783346 := by decide +kernel

theorem rows225C_108 : rowsJ 62 63 44 50 ≤ 81263789896013 := by decide +kernel

theorem rows225C_109 : rowsJ 62 63 50 55 ≤ 79817827539418 := by decide +kernel

theorem rows225C_110 : rowsJ 62 63 55 59 ≤ 91066193524407 := by decide +kernel

theorem rows225C_111 : rowsJ 62 63 59 400 ≤ 126520729750463 := by decide +kernel

theorem rows225C_112 : rowsJ 63 64 0 35 ≤ 813933005523631 := by decide +kernel

theorem rows225C_113 : rowsJ 63 64 35 44 ≤ 176150328584924 := by decide +kernel

theorem rows225C_114 : rowsJ 63 64 44 50 ≤ 76684855398400 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_107
#print axioms SieveCert.rows225C_114
