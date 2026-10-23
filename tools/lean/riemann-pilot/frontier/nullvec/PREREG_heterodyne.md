# Pre-registration 21: is the heterodyne the mechanism? (round 107)

Committed before any model kernel is built.

**Reference.** The first-order per-prime responses `Δ₁^{(p)}` with the true kernel (round 106): `p = 2` gives the strongest tone at **9.47**, and `p = 3` at **16.75**.

**Model kernels**, built per window from round 106's kernel dumps:
- **M1, smooth only.** `S(w)`: the kernel smoothed in `γ` with a Gaussian of width 3 local node spacings, separately inside (`r < r_e`) and outside. This removes the node-scale sign oscillation.
- **M2, heterodyne.** `S(w)` plus, beyond the edge, one wave `E(r)·[c₁ cos κγ + c₂ sin κγ]`:
  - `E(r)` is the smoothed envelope `√2·S(|w − S(w)|)`;
  - `κ` is the wavenumber in `[0.2, 5]` that best matches `w − S(w)` for `r ∈ [r_e, 2.2]`;
  - `c₁` and `c₂` are least-squares coefficients.

  M2 has three shape numbers per window (`κ`, `c₁`, `c₂`) and no information about the primes.

**Hypothesis HET.**
- **(a)** M2 gives the strongest tone within `±0.3` of 9.47 for `p = 2` and of 16.75 for `p = 3`.
- **(b)** M1 does not, i.e. at least one of the two misses by more than 0.3.

HET passes if (a) and (b) both hold. It then says that the tones come from the prime waves beating against the kernel's window-frequency oscillation beyond the edge.

**Also reported:**
- the fraction of the oscillatory part's variance that the single wave captures;
- the fitted `κ(x)` against `ln x`.
