# Pre-registration 11: is the chain a resonator? (round 97)

Committed before any noise-driven zero set is generated.

**Observation behind it** (post hoc, round 96 with interpolated peaks). The same line frequencies recur whichever primes drive the chain:
- ≈ 9.4 appears with the true zeros, only-2, only-7 and minus-2, and at 9.60 with only-3;
- ≈ 5.0–5.2 appears in 5 of 6 chains;
- 16.75 appears with the true zeros, only-3 and minus-2.

The smooth quantiles (no fluctuation) give no lines.

**Hypothesis RES.** The line positions are intrinsic modes of the window chain, i.e. of the Γ side. The arithmetic only *excites* them. So a non-arithmetic excitation of the same size must produce the same lines.

**The alternative, ARITH.** The lines need the arithmetic structure of the fluctuations.

**Excitations.** The base is the smooth quantiles `θ(γ̃_k) = (k − 3/2)π`, `γ < 1000`, as in rounds 91 and 95.
- **N1, white.** Add i.i.d. Gaussian jitter with sd `0.383`, which gives the true zeros' mean |deviation| of 0.306. Re-sort.
- **N2, random-phase primes.** Use `S(t) = −(1/π) Σ_{p ≤ 101} Im log(1 − p^{−½} e^{−i(t ln p + φ_p)})`, with i.i.d. uniform phases `φ_p`. This keeps the frequencies `ln p` but destroys the arithmetic phase coherence. Zeros come from `θ/π + 1 + S = k − ½`, taking all crossings with `t ≥ 10`.

Each excitation is run with 4 seeds (seed = 1, 2, 3, 4), using round 95's fast kernel and grid (`x ∈ [3, 12]`, step 0.04).

**Line detection** (as in round 96's interpolated re-read). Take the residual after the smooth fit, then a Hann window and a 16× zero-padded spectrum. Local maxima are taken in `[1.5, 30]`. A target line is **present** if:
- there is a local maximum within `±0.3` of the target;
- its power is `≥ 0.3` of the strongest peak in `[1.5, 30]`;
- it exceeds the 95th percentile of the padded spectrum over `[target − 5, target + 5]`, with `±1` excluded.

**Criteria.**
- **RES passes** if, under N1 (white), the 9.42 line is present in `≥ 3` of the 4 seeds, and at least one of 4.97 and 16.75 is present in `≥ 3` of the 4 seeds.
- **ARITH holds** if the 9.42 line is present in `≤ 1` of the 4 white seeds.
- N2 is scored the same way but does not decide.

**Expectation, stated before computing.** Genuinely unknown. Round 91 shows that *some* fluctuation is needed. Whether its arithmetic character matters is exactly what is untested.
