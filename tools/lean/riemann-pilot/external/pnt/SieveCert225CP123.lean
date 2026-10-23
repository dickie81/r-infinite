/-
# Round 625: the certificate at `L = 9/4`, parts 1000–1008 of 1374

File 123 of 167: the parts `rows225C_1000` … `rows225C_1008` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (9 parts, 58952 depth-4 tests: row 146 columns 79–82, row 146 columns 83–87, row 146
columns 88–93, row 146 columns 94–100, row 146 columns 101–399, row 147 columns 0–59, row 147 columns 60–65, row 147
columns 66–69, row 147 columns 70–73), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide
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

theorem rows225C_1000 : rowsJ 146 147 79 83 ≤ 2073453497212 := by decide +kernel

theorem rows225C_1001 : rowsJ 146 147 83 88 ≤ 250753754329 := by decide +kernel

theorem rows225C_1002 : rowsJ 146 147 88 94 ≤ 0 := by decide +kernel

theorem rows225C_1003 : rowsJ 146 147 94 101 ≤ 7242544355909 := by decide +kernel

theorem rows225C_1004 : rowsJ 146 147 101 400 ≤ 611043508376502 := by decide +kernel

theorem rows225C_1005 : rowsJ 147 148 0 60 ≤ 151006902126543 := by decide +kernel

theorem rows225C_1006 : rowsJ 147 148 60 66 ≤ 10793967742427 := by decide +kernel

theorem rows225C_1007 : rowsJ 147 148 66 70 ≤ 11644461771438 := by decide +kernel

theorem rows225C_1008 : rowsJ 147 148 70 74 ≤ 11343712353823 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_1000
#print axioms SieveCert.rows225C_1008
