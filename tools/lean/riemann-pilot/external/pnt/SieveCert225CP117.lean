/-
# Round 625: the certificate at `L = 9/4`, parts 952–959 of 1374

File 117 of 167: the parts `rows225C_952` … `rows225C_959` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (8 parts, 53289 depth-4 tests: row 141 columns 91–95, row 141 columns 96–101, row 141
columns 102–399, row 142 columns 0–60, row 142 columns 61–67, row 142 columns 68–71, row 142 columns 72–74, row 142
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

theorem rows225C_952 : rowsJ 141 142 91 96 ≤ 0 := by decide +kernel

theorem rows225C_953 : rowsJ 141 142 96 102 ≤ 8175424428465 := by decide +kernel

theorem rows225C_954 : rowsJ 141 142 102 400 ≤ 803931040913966 := by decide +kernel

theorem rows225C_955 : rowsJ 142 143 0 61 ≤ 188088069473297 := by decide +kernel

theorem rows225C_956 : rowsJ 142 143 61 68 ≤ 9366486751423 := by decide +kernel

theorem rows225C_957 : rowsJ 142 143 68 72 ≤ 7815921281715 := by decide +kernel

theorem rows225C_958 : rowsJ 142 143 72 75 ≤ 5335211734004 := by decide +kernel

theorem rows225C_959 : rowsJ 142 143 75 79 ≤ 3538260176916 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_952
#print axioms SieveCert.rows225C_959
