/-
# Round 631: the grid of the certificate at `L = 2285/1000` (the unconditional exponent under round 619's `total < K`)

The grid of `SieveTypeIIU2285.typeII_2285`'s window: `U1 = ⌈(40302/100000)DEN⌉`, `U2 = ⌊(47464/100000)DEN⌋`, `n = 250`
(`grid2285U`, `gridOK2285U`). Its certificate is checked by the kernel in 252 parts, 28 files
(`SieveCert2285UP1.lean` … `SieveCert2285UP28.lean`, one `lean` process each): ranges of consecutive rows, and the
78 heavy rows in column pieces (`SieveCertColsDefs.rowsJ`), each part of at most 8000 depth-4 tests and each
file of at most 60000, as round 625's; assembled in `SieveCert2285U.lean`.

The file imports `SieveCertColsDefs.lean`, which imports `SieveCertDefs.lean` only, so neither it nor the part files
load `Mathlib` (round 618).
-/
import SieveCertColsDefs

namespace SieveCert

/-- **The grid at `L = 2285/1000`**: `U1 = ⌈(40302/100000)DEN⌉`, `U2 = ⌊(47464/100000)DEN⌋`, `n = 250`. -/
@[instance_reducible] def grid2285U : Grid := ⟨(40302 * DEN + 99999) / 100000, 47464 * DEN / 100000, 250⟩

theorem gridOK2285U : @GridOK grid2285U :=
  @GridOK.mk grid2285U (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

end SieveCert

#print axioms SieveCert.gridOK2285U
