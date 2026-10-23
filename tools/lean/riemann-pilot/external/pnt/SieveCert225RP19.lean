/-
# Round 705: the refined certificate at `L = 9/4` with `n = 200`, parts 77–82 of 117

File 19 of 27: the parts `rows225R_77` … `rows225R_82` of `SieveCert225R.lean`'s certificate on
`SieveGrid225R.grid225R` (6 parts, 27889 tests: row 73 columns 0–44, row 73 columns 45–199, row 74 columns 0–45, row
74 columns 46–199, row 75 columns 0–45, row 75 columns 46–199), each a sum of refined costs (`rows2` or `rowsJ2`) at
most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid225R.lean`.
-/
import SieveGrid225R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid225R

theorem rows225R_77 : rowsJ2 73 74 0 45 ≤ 589871022669516 := by decide +kernel

theorem rows225R_78 : rowsJ2 73 74 45 200 ≤ 781804105373912 := by decide +kernel

theorem rows225R_79 : rowsJ2 74 75 0 46 ≤ 573425616175395 := by decide +kernel

theorem rows225R_80 : rowsJ2 74 75 46 200 ≤ 769905838115669 := by decide +kernel

theorem rows225R_81 : rowsJ2 75 76 0 46 ≤ 546432305569152 := by decide +kernel

theorem rows225R_82 : rowsJ2 75 76 46 200 ≤ 521184904959847 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225R_77
#print axioms SieveCert.rows225R_82
