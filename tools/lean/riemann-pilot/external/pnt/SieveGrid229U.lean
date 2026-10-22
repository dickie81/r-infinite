/-
# Round 623: the grid of the certificate at `L = 229/100` (the unconditional exponent under round 619's `total < K`)

The grid of `SieveTypeIIU229.typeII_229`'s window: `U1 = ⌈(40011/100000)DEN⌉`, `U2 = ⌊(47579/100000)DEN⌋`, `n = 150`
(`grid229U`, `gridOK229U`). Its certificate is checked by the kernel in 21 parts of consecutive rows, in the 5 files
`SieveCert229UP1.lean` … `SieveCert229UP5.lean` (one `lean` process each: within one file the parts' memory
accumulates, round 614; round 625: not borne out as the cause, the peaks following each file's largest part on the
ten part files of rounds 614, as rebuilt in round 619, and 623, README round 626 and review of round 624, finding 1;
round 632: "on the ten part files" added, round 625's files not following that law, README round 632 and review of
round 625, F3; round 633: "as rebuilt in round 619" added, the law being fitted to that rebuild's peaks, as
`SieveGrid226.lean` says, README round 633 and review of round 631, F-E), and assembled in `SieveCert229U.lean`.
Round 607's `grid229` (`SieveCert229.lean`) is the grid of the conditional exponent `229/100`; this one is of the
unconditional route's window.

The file imports `SieveCertDefs.lean`, so neither it nor the part files load `Mathlib` (round 618).
-/
import SieveCertDefs

namespace SieveCert

/-- **The grid at `L = 229/100`**: `U1 = ⌈(40011/100000)DEN⌉`, `U2 = ⌊(47579/100000)DEN⌋`, `n = 150`. -/
@[instance_reducible] def grid229U : Grid := ⟨(40011 * DEN + 99999) / 100000, 47579 * DEN / 100000, 150⟩

theorem gridOK229U : @GridOK grid229U :=
  @GridOK.mk grid229U (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

end SieveCert

#print axioms SieveCert.gridOK229U
