# Pre-registration 28: the window chain rebuilt on the prime side (round 118)

**The object.** `kprimeside.py` builds the window Gram matrix from the prime side of the Guinand–Weil explicit formula. It uses only the poles, the archimedean `Re ψ(¼ + ir/2)`, `log π` and `Σ_{n ≤ x} Λ(n) n^{−½} G(log n)`, with every entry in closed form and no zero used. This matrix equals `½ Σ_ρ |ĝ(γ_ρ)|²` over **all** zeros as an identity, whether or not RH holds. So its chain `lnK(x) = log((2a)²(M⁻¹)₀₀)` is defined without RH.

**Construction checks, done before this registration and not evidence for the tones.**
- Entries match a direct sum over the 6700 known zeros plus a smooth tail to `5·10⁻⁵`, which is the tail model's accuracy (`kprimeside_check.py`).
- Entries match an independent u-space quadrature to `5·10⁻¹⁶` (`kps_indep.py`).
- On the smallest-eigenvalue direction at `x = 9`, `K = 7`, the prime side gives `1.655·10⁻¹⁷` and the zero side gives `1.641·10⁻¹⁷ + 0.013·10⁻¹⁷` (tail).
- **A bug was found and fixed:** `ln x` taken as a double shifts the window edge by `10⁻¹⁶` against the exact prime positions `ln n` and makes the form indefinite. `x` is now an exact decimal.
- Spot values: `lnK` = 16.960, 51.254, 86.865, 123.243 at `x` = 3, 6, 9, 12. The zero-side `r95` gives 16.969, 51.276, 86.894, 123.285.
- **Single-prime forms (Γ + one prime) are not usable.** They are small (`lnK ≈ 1`) and often indefinite, because the chain's deep structure is collective. No per-prime attribution is registered.

**Run.** `x = 3.00, 3.04, …, 12.00` (226 windows), `Kfac = 15`, adaptive precision (`kprimeside.py`, output `rPS_*.jsonl`).

**Criteria (`kprimeside_score.py`, committed now). The zero side is `r95_true.jsonl`: zeros below 1000 plus a smooth tail to 6997.**
- **P1:** the correlation of the residual wiggles (the rounds 106–116 basis `e^d, d, 1, e^{−d}`) between the prime-side and zero-side chains is ≥ 0.95.
- **P2:** the prime-side chain's strongest line lies within ±0.3 of the law's `3π = 9.425`.
- **P3:** the prime-side and zero-side chains' top-4 lines agree pairwise to within ±0.2.
- **Reported:**
  - the max `|ΔlnK|`, the wiggle rms of the prime-side chain and of the difference, and the difference's lines. The difference comes from the zero side's truncation and tail model; it is expected small and not to carry the tone lines.

**What a pass would mean.** The tones seen since round 100 are properties of an object defined by primes and Γ alone, not of an RH-conditional zero-side construction. It says nothing about RH itself.
