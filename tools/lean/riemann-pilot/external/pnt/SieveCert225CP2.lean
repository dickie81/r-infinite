/-
# Round 625: the certificate at `L = 9/4`, parts 10–19 of 1374

File 2 of 167: the parts `rows225C_10` … `rows225C_19` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (10 parts, 53025 depth-4 tests: rows 33–33, rows 34–34, row 35 columns 0–34, row 35 columns
35–399, row 36 columns 0–34, row 36 columns 35–399, row 37 columns 0–34, row 37 columns 35–399, row 38 columns 0–34,
row 38 columns 35–399), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide +kernel`, one at a
time (`Elab.async false`).

The file imports `SieveGrid225C.lean`.
-/
import SieveGrid225C

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid225C

theorem rows225C_10 : rows 33 34 ≤ 1237057468634004 := by decide +kernel

theorem rows225C_11 : rows 34 35 ≤ 1304106144976099 := by decide +kernel

theorem rows225C_12 : rowsJ 35 36 0 35 ≤ 1289467070124406 := by decide +kernel

theorem rows225C_13 : rowsJ 35 36 35 400 ≤ 79959699579620 := by decide +kernel

theorem rows225C_14 : rowsJ 36 37 0 35 ≤ 1274929237591114 := by decide +kernel

theorem rows225C_15 : rowsJ 36 37 35 400 ≤ 157250777827009 := by decide +kernel

theorem rows225C_16 : rowsJ 37 38 0 35 ≤ 1260403798529204 := by decide +kernel

theorem rows225C_17 : rowsJ 37 38 35 400 ≤ 231028024243790 := by decide +kernel

theorem rows225C_18 : rowsJ 38 39 0 35 ≤ 1245881500051889 := by decide +kernel

theorem rows225C_19 : rowsJ 38 39 35 400 ≤ 300341977722093 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_10
#print axioms SieveCert.rows225C_19
