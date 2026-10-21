/-
# Round 625: the certificate at `L = 9/4`, parts 0–9 of 1374

File 1 of 167: the parts `rows225C_0` … `rows225C_9` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (10 parts, 58905 depth-4 tests: rows 0–18, rows 19–22, rows 23–24, rows 25–26, rows 27–27,
rows 28–28, rows 29–29, rows 30–30, rows 31–31, rows 32–32), each a sum of costs (`rows` or `rowsJ`) at most its
bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid225C.lean`.
-/
import SieveGrid225C

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid225C

theorem rows225C_0 : rows 0 19 ≤ 2321664898196491 := by decide +kernel

theorem rows225C_1 : rows 19 23 ≤ 1940598384317231 := by decide +kernel

theorem rows225C_2 : rows 23 25 ≤ 1279125069567760 := by decide +kernel

theorem rows225C_3 : rows 25 27 ≤ 1506420812048410 := by decide +kernel

theorem rows225C_4 : rows 27 28 ≤ 843048358242409 := by decide +kernel

theorem rows225C_5 : rows 28 29 ≤ 905246958568417 := by decide +kernel

theorem rows225C_6 : rows 29 30 ≤ 969084241401993 := by decide +kernel

theorem rows225C_7 : rows 30 31 ≤ 1034488275220801 := by decide +kernel

theorem rows225C_8 : rows 31 32 ≤ 1101388255934880 := by decide +kernel

theorem rows225C_9 : rows 32 33 ≤ 1169185308763892 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_0
#print axioms SieveCert.rows225C_9
