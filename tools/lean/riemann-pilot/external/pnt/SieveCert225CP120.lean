/-
# Round 625: the certificate at `L = 9/4`, parts 976–983 of 1374

File 120 of 167: the parts `rows225C_976` … `rows225C_983` of `SieveCert225C.lean`'s certificate on
`SieveGrid225C.grid225C` (8 parts, 55962 depth-4 tests: row 144 columns 61–66, row 144 columns 67–70, row 144
columns 71–73, row 144 columns 74–77, row 144 columns 78–81, row 144 columns 82–85, row 144 columns 86–90, row 144
columns 91–96), each a sum of costs (`rows` or `rowsJ`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows225C_976 : rowsJ 144 145 61 67 ≤ 9295957596614 := by decide +kernel

theorem rows225C_977 : rowsJ 144 145 67 71 ≤ 9363236725059 := by decide +kernel

theorem rows225C_978 : rowsJ 144 145 71 74 ≤ 7038361376149 := by decide +kernel

theorem rows225C_979 : rowsJ 144 145 74 78 ≤ 5583813814448 := by decide +kernel

theorem rows225C_980 : rowsJ 144 145 78 82 ≤ 2038663913006 := by decide +kernel

theorem rows225C_981 : rowsJ 144 145 82 86 ≤ 113961055630 := by decide +kernel

theorem rows225C_982 : rowsJ 144 145 86 91 ≤ 0 := by decide +kernel

theorem rows225C_983 : rowsJ 144 145 91 97 ≤ 359894191897 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows225C_976
#print axioms SieveCert.rows225C_983
