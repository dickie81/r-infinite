/-
# Round 625: the grid of the certificate at `L = 9/4` (under `CGLDensity` alone, round 619's `total < K`)

The grid of `SieveTypeIIU225C.typeII_225c`'s window: `U1 = ⌈(41191/100000)DEN⌉`, `U2 = ⌊(48127/100000)DEN⌋`, `n = 400`
(`grid225C`, `gridOK225C`). Its certificate is checked by the kernel in 1374 parts, 167 files
(`SieveCert225CP1.lean` … `SieveCert225CP167.lean`, one `lean` process each): ranges of consecutive rows, and the
181 heavy rows in column pieces (`SieveCertColsDefs.rowsJ`), each file of at most 60000 depth-4 tests, the measure
of the kernel's memory and time; assembled in `SieveCert225C.lean`.

The file imports `SieveCertColsDefs.lean`, which imports `SieveCertDefs.lean` only, so neither it nor the part files
load `Mathlib` (round 618).
-/
import SieveCertColsDefs

namespace SieveCert

/-- **The grid at `L = 9/4`**: `U1 = ⌈(41191/100000)DEN⌉`, `U2 = ⌊(48127/100000)DEN⌋`, `n = 400`. -/
@[instance_reducible] def grid225C : Grid := ⟨(41191 * DEN + 99999) / 100000, 48127 * DEN / 100000, 400⟩

theorem gridOK225C : @GridOK grid225C :=
  @GridOK.mk grid225C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

end SieveCert

#print axioms SieveCert.gridOK225C
