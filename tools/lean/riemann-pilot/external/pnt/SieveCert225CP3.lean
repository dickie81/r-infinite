/-
# Round 625: the certificate at `L = 9/4`, parts 20–28 of 1374

File 3 of 167: the parts `rows225C_20` … `rows225C_28` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (9 parts, 59025 depth-4 tests: row 39 columns 0–34, row 39 columns 35–399, row 40 columns
0–34, row 40 columns 35–399, row 41 columns 0–34, row 41 columns 35–399, row 42 columns 0–34, row 42 columns 35–399,
row 43 columns 0–34), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows225C_20 : rowsJ 39 40 0 35 ≤ 1231350333180997 := by decide +kernel

theorem rows225C_21 : rowsJ 39 40 35 400 ≤ 364291759592976 := by decide +kernel

theorem rows225C_22 : rowsJ 40 41 0 35 ≤ 1216801060859512 := by decide +kernel

theorem rows225C_23 : rowsJ 40 41 35 400 ≤ 421855384667034 := by decide +kernel

theorem rows225C_24 : rowsJ 41 42 0 35 ≤ 1202142494073653 := by decide +kernel

theorem rows225C_25 : rowsJ 41 42 35 400 ≤ 472042691487636 := by decide +kernel

theorem rows225C_26 : rowsJ 42 43 0 35 ≤ 1187444130401435 := by decide +kernel

theorem rows225C_27 : rowsJ 42 43 35 400 ≤ 513846200774637 := by decide +kernel

theorem rows225C_28 : rowsJ 43 44 0 35 ≤ 1172613396981019 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_20
#print axioms SieveCert.rows225C_28
