/-
# Round 621: the certificate of the sieve route's loss at `L = 230/100` (the unconditional exponent under
Halász–Montgomery per bin)

The grid of the window `[3944/10000, 4780/10000]` (the Halász–Montgomery window of the curve `gU` at `L = 230/100`,
the scan of `SIEVE-ROUTE.md` §20): `U1 = ⌈(3944/10000)DEN⌉`, `U2 = ⌊(4780/10000)DEN⌋`, `n = 100`. On it
`SieveCert.total` is at most `0.88K`, checked by the kernel in one check.

The file imports `SieveCertDefs.lean`, so the check runs without Mathlib's environment.
-/
import SieveCertDefs

namespace SieveCert

/-- **The grid at `L = 230/100`**: `U1 = ⌈(3944/10000)DEN⌉`, `U2 = ⌊(4780/10000)DEN⌋`, `n = 100`. -/
@[instance_reducible] def grid230 : Grid := ⟨(3944 * DEN + 9999) / 10000, 4780 * DEN / 10000, 100⟩

theorem gridOK230 : @GridOK grid230 :=
  @GridOK.mk grid230 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- **The certificate on `grid230`**: the loss's bound is at most `0.88`, checked by the kernel. -/
theorem total_le_230 : @total grid230 ≤ 88 * K / 100 := by decide +kernel

end SieveCert

#print axioms SieveCert.gridOK230
#print axioms SieveCert.total_le_230
