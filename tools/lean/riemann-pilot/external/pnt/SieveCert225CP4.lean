/-
# Round 625: the certificate at `L = 9/4`, parts 29–38 of 1374

File 4 of 167: the parts `rows225C_29` … `rows225C_38` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (10 parts, 59345 depth-4 tests: row 43 columns 35–399, row 44 columns 0–34, row 44 columns
35–43, row 44 columns 44–399, row 45 columns 0–34, row 45 columns 35–43, row 45 columns 44–399, row 46 columns 0–34,
row 46 columns 35–43, row 46 columns 44–399), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide
+kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid225C.lean`.
-/
import SieveGrid225C

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid225C

theorem rows225C_29 : rowsJ 43 44 35 400 ≤ 547415315592240 := by decide +kernel

theorem rows225C_30 : rowsJ 44 45 0 35 ≤ 1157640384248635 := by decide +kernel

theorem rows225C_31 : rowsJ 44 45 35 44 ≤ 526433642638292 := by decide +kernel

theorem rows225C_32 : rowsJ 44 45 44 400 ≤ 46865369240512 := by decide +kernel

theorem rows225C_33 : rowsJ 45 46 0 35 ≤ 1142510935233018 := by decide +kernel

theorem rows225C_34 : rowsJ 45 46 35 44 ≤ 505433509516020 := by decide +kernel

theorem rows225C_35 : rowsJ 45 46 44 400 ≤ 86561579835128 := by decide +kernel

theorem rows225C_36 : rowsJ 46 47 0 35 ≤ 1127214743693146 := by decide +kernel

theorem rows225C_37 : rowsJ 46 47 35 44 ≤ 484435809879712 := by decide +kernel

theorem rows225C_38 : rowsJ 46 47 44 400 ≤ 119596405339050 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_29
#print axioms SieveCert.rows225C_38
