/-
# Round 625: the certificate at `L = 9/4`, parts 1340–1349 of 1374

File 164 of 167: the parts `rows225C_1340` … `rows225C_1349` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (10 parts, 55333 depth-4 tests: row 208 columns 0–39, row 208 columns 40–399, row 209
columns 0–39, row 209 columns 40–399, row 210 columns 0–38, row 210 columns 39–399, row 211 columns 0–38, row 211
columns 39–399, row 212 columns 0–38, row 212 columns 39–399), each a sum of costs (`rows` or `rowsJ`) at most its
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

theorem rows225C_1340 : rowsJ 208 209 0 40 ≤ 64237714462377 := by decide +kernel

theorem rows225C_1341 : rowsJ 208 209 40 400 ≤ 2314208672784599 := by decide +kernel

theorem rows225C_1342 : rowsJ 209 210 0 40 ≤ 70005352694061 := by decide +kernel

theorem rows225C_1343 : rowsJ 209 210 40 400 ≤ 2397412700854245 := by decide +kernel

theorem rows225C_1344 : rowsJ 210 211 0 39 ≤ 64143576806187 := by decide +kernel

theorem rows225C_1345 : rowsJ 210 211 39 400 ≤ 2492351438543706 := by decide +kernel

theorem rows225C_1346 : rowsJ 211 212 0 39 ≤ 69907703882621 := by decide +kernel

theorem rows225C_1347 : rowsJ 211 212 39 400 ≤ 2574907462403195 := by decide +kernel

theorem rows225C_1348 : rowsJ 212 213 0 39 ≤ 75968999331206 := by decide +kernel

theorem rows225C_1349 : rowsJ 212 213 39 400 ≤ 2657264089878806 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_1340
#print axioms SieveCert.rows225C_1349
