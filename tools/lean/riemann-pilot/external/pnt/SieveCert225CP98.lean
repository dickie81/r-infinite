/-
# Round 625: the certificate at `L = 9/4`, parts 793–800 of 1374

File 98 of 167: the parts `rows225C_793` … `rows225C_800` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (8 parts, 56512 depth-4 tests: row 128 columns 75–78, row 128 columns 79–81, row 128
columns 82–84, row 128 columns 85–87, row 128 columns 88–90, row 128 columns 91–94, row 128 columns 95–98, row 128
columns 99–103), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows225C_793 : rowsJ 128 129 75 79 ≤ 0 := by decide +kernel

theorem rows225C_794 : rowsJ 128 129 79 82 ≤ 0 := by decide +kernel

theorem rows225C_795 : rowsJ 128 129 82 85 ≤ 0 := by decide +kernel

theorem rows225C_796 : rowsJ 128 129 85 88 ≤ 0 := by decide +kernel

theorem rows225C_797 : rowsJ 128 129 88 91 ≤ 0 := by decide +kernel

theorem rows225C_798 : rowsJ 128 129 91 95 ≤ 0 := by decide +kernel

theorem rows225C_799 : rowsJ 128 129 95 99 ≤ 735193559871 := by decide +kernel

theorem rows225C_800 : rowsJ 128 129 99 104 ≤ 6005872668889 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_793
#print axioms SieveCert.rows225C_800
