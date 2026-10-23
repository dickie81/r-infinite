/-
# Round 625: the certificate at `L = 9/4`, parts 72–80 of 1374

File 9 of 167: the parts `rows225C_72` … `rows225C_80` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (9 parts, 56205 depth-4 tests: row 55 columns 55–399, row 56 columns 0–34, row 56 columns
35–43, row 56 columns 44–49, row 56 columns 50–54, row 56 columns 55–399, row 57 columns 0–34, row 57 columns 35–43,
row 57 columns 44–49), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide +kernel`, one at a time
(`Elab.async false`).

The file imports `SieveGrid225C.lean`.
-/
import SieveGrid225C

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid225C

theorem rows225C_72 : rowsJ 55 56 55 400 ≤ 20399487744112 := by decide +kernel

theorem rows225C_73 : rowsJ 56 57 0 35 ≤ 957537679447747 := by decide +kernel

theorem rows225C_74 : rowsJ 56 57 35 44 ≤ 286221895570701 := by decide +kernel

theorem rows225C_75 : rowsJ 56 57 44 50 ≤ 119124087807915 := by decide +kernel

theorem rows225C_76 : rowsJ 56 57 50 55 ≤ 91218099848811 := by decide +kernel

theorem rows225C_77 : rowsJ 56 57 55 400 ≤ 41283663294942 := by decide +kernel

theorem rows225C_78 : rowsJ 57 58 0 35 ≤ 938248188404644 := by decide +kernel

theorem rows225C_79 : rowsJ 57 58 35 44 ≤ 268776996489753 := by decide +kernel

theorem rows225C_80 : rowsJ 57 58 44 50 ≤ 111589688224769 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_72
#print axioms SieveCert.rows225C_80
