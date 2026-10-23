# Pre-registration 14: the height-to-frequency law ω(r) (round 100)

Committed before any fine-ladder chain is computed.

**Construction.** This is round 99's keep-B (`kzeroside3.py`), with narrow bands `B_j = [0.9 + 0.1j, 1.0 + 0.1j)`, `j = 0, …, 15`, covering `r ∈ [0.9, 2.5)`. That gives 16 chains on the grid `x ∈ [3, 12]`, 226 windows. For each band, `ω_j` is the strongest local maximum of the interpolated spectrum (round 97's method: 16× zero padding) in `[4, 35]`. We also report its relative power and the second peak.

**Linear-response reference, derived before computing.** Suppose a band's contribution is linear in the zero displacements, `δγ ≈ −S(γ)/ρ(γ)` with `S(γ) ≈ −(1/π)Σ_p p^{−½} sin(γ ln p)`. A band at `r` spans `γ ∈ 4πx[r, r + Δr]`. It then oscillates in `x` at `ω = 4π r ln p` for each prime. The dominant `p = 2` term gives `ω = 8.71 r`: that is 9.6 at `r = 1.1`, 13.1 at `r = 1.5` and 16.5 at `r = 1.9`. Round 99's coarse bands (9.1–9.4, 16.6–16.75, 23.3–23.6) already disagree with this above `r ≈ 1.3`. It is recorded as the reference, not as a hypothesis expected to pass.

**Hypotheses.**
- **LIN (continuous law).** The 16 `ω_j` fit a straight line in `r` with rms residual `≤ 0.6`, and no two adjacent bands differ by more than 3.
- **STAIR (quantised family).** For every band with `r ≥ 1.0`, `ω_j` lies within `±0.6` of one of `{9.42, 16.75, 23.6}`. The bands assigned to each value form one contiguous run of at least 2 bands, and the value never decreases as `r` increases.

At most one of LIN and STAIR can pass. If neither passes, `ω(r)` is reported as measured.

**Expectation.** Round 99 hints at STAIR: equal steps of ≈ 7.2 every `Δr ≈ 0.4`. A staircase would mean the window turns a continuum of heights into a discrete family, which is the thing to derive. LIN with a slope other than 8.71 would instead mean a dispersion law different from linear response.
