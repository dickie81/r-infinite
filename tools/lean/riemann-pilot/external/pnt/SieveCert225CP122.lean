/-
# Round 625: the certificate at `L = 9/4`, parts 992–999 of 1374

File 122 of 167: the parts `rows225C_992` … `rows225C_999` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (8 parts, 54930 depth-4 tests: row 145 columns 88–93, row 145 columns 94–100, row 145
columns 101–399, row 146 columns 0–60, row 146 columns 61–66, row 146 columns 67–70, row 146 columns 71–74, row 146
columns 75–78), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows225C_992 : rowsJ 145 146 88 94 ≤ 0 := by decide +kernel

theorem rows225C_993 : rowsJ 145 146 94 101 ≤ 6923129422371 := by decide +kernel

theorem rows225C_994 : rowsJ 145 146 101 400 ≤ 610510741791800 := by decide +kernel

theorem rows225C_995 : rowsJ 146 147 0 61 ≤ 158465044793497 := by decide +kernel

theorem rows225C_996 : rowsJ 146 147 61 67 ≤ 11247827648660 := by decide +kernel

theorem rows225C_997 : rowsJ 146 147 67 71 ≤ 11204860885709 := by decide +kernel

theorem rows225C_998 : rowsJ 146 147 71 75 ≤ 9916402234467 := by decide +kernel

theorem rows225C_999 : rowsJ 146 147 75 79 ≤ 5281550682902 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_992
#print axioms SieveCert.rows225C_999
