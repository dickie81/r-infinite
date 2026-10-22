/-
# Round 614: the grid of the certificate at `L = 226/100`

The grid of `SieveTypeIIU226.typeII_226`'s window: `U1 = ⌈(4075/10000)DEN⌉`, `U2 = ⌊(4835/10000)DEN⌋`, `n = 200`
(`grid226`, `gridOK226`). Its certificate is checked by the kernel in 49 parts of consecutive rows, in the 5 files
`SieveCert226P1.lean` … `SieveCert226P5.lean` (one `lean` process each: within one file the parts' memory accumulates,
and one file of 35 parts, with Mathlib loaded as before round 618, was killed at 13.0 GiB resident, the shell's cgroup
limit being 13.36 GiB), and assembled in `SieveCert226.lean`. (Round 625: the accumulation is not borne out as the
cause: on the ten part files of rounds 614, as rebuilt in round 619, and 623 the peaks follow each file's largest
part, and a term in a file's total tests adds about 0.006 GiB per thousand; README, round 626; review of round 624,
finding 1.)

The file imports `SieveCertDefs.lean` (round 618; until then `SieveCert232.lean`, for `rows` and `rows_eq`), so neither
it nor the part files load `Mathlib` (they load `Mathlib.Init`'s closure, 1,339 modules; round 619).
-/
import SieveCertDefs

namespace SieveCert

/-- **The grid at `L = 226/100`**: `U1 = ⌈(4075/10000)DEN⌉`, `U2 = ⌊(4835/10000)DEN⌋`, `n = 200`. -/
@[instance_reducible] def grid226 : Grid := ⟨(4075 * DEN + 9999) / 10000, 4835 * DEN / 10000, 200⟩

theorem gridOK226 : @GridOK grid226 :=
  @GridOK.mk grid226 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

end SieveCert

#print axioms SieveCert.gridOK226
