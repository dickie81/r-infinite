/-
# Round 625: the certificate at `L = 9/4`, parts 189–196 of 1374

File 23 of 167: the parts `rows225C_189` … `rows225C_196` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (8 parts, 56020 depth-4 tests: row 73 columns 35–43, row 73 columns 44–49, row 73 columns
50–54, row 73 columns 55–58, row 73 columns 59–63, row 73 columns 64–69, row 73 columns 70–399, row 74 columns
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

theorem rows225C_189 : rowsJ 73 74 35 44 ≤ 71237549087554 := by decide +kernel

theorem rows225C_190 : rowsJ 73 74 44 50 ≤ 59303262764344 := by decide +kernel

theorem rows225C_191 : rowsJ 73 74 50 55 ≤ 100289651988005 := by decide +kernel

theorem rows225C_192 : rowsJ 73 74 55 59 ≤ 128181018477975 := by decide +kernel

theorem rows225C_193 : rowsJ 73 74 59 64 ≤ 171336516588378 := by decide +kernel

theorem rows225C_194 : rowsJ 73 74 64 70 ≤ 183663377042348 := by decide +kernel

theorem rows225C_195 : rowsJ 73 74 70 400 ≤ 108842661318827 := by decide +kernel

theorem rows225C_196 : rowsJ 74 75 0 35 ≤ 563705714778804 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_189
#print axioms SieveCert.rows225C_196
