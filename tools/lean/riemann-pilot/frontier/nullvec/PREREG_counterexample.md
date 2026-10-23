# Pre-registration 29: the signature of a counterexample in the window chain (round 119)

**Setup.**
- Start from the certified prime-side form `M(x)` (round 119 part 1: positive-definite at all 226 windows).
- Hypothesis `H(n, δ)`: the true consecutive zeros `γ_n, γ_{n+1}` collide at `γ₀ = (γ_n + γ_{n+1})/2` and leave the line as `ρ = ½ ± δ + iγ₀`. This is a legal quadruple, and the zero count is preserved.
- Then `ΔM = 2 Re[v vᵀ] − u_n u_nᵀ − u_{n+1} u_{n+1}ᵀ`, with `v = ĝ(γ₀ + iδ)` and `u = ĝ(γ)` (`kcounter.py`).
- The zeros are taken to 210 digits (`zeros_hp.json`).
- **Outputs:** positivity of `M + ΔM` by certified Cholesky (PD / LOST), the exact `Δ lnK`, and the first-order `Δ₁ lnK = −yᵀΔMy/s` from round 113's `response_kernel`.

**Seen before registering (construction check, `CT_REMOVE_ONLY=1`).**
- Removing the pairs `n = 4, 13, 30` (`γ₀ = 31.7, 60.1, 102.5`) keeps the form positive-definite, as it must.
- `Δ lnK` is small outside the kernel horizon and large inside it. For `n = 30`: +0.046 and +0.057 at `x = 3, 6`; +4.0 and +7.4 at `x = 9, 12`.
- First order is badly wrong inside the horizon (e.g. `10⁻⁴²` vs 17.9), because the ground state vanishes at the zeros and reshapes non-perturbatively.
- So the horizon prediction below is informed by these four `x` values. It is not blind.

**Cases.** `n ∈ {4, 13, 30}` and `δ ∈ {0.001, 0.01, 0.1}`, on `x = 3.00, 3.04, …, 12.00`. The horizon `x_h(γ₀) = γ₀/(4π · 0.8613)`, from round 106's kernel edge `r_e = 0.8613`, is 2.93, 5.55 and 9.47.

**Predictions (`kcounter_score.py`, committed now).**
- **S1 (horizon):** no certified loss of positivity at `x < 0.9 x_h`, for any case.
- **S2 (detection):** for every case with `1.3 x_h ≤ 12` (`n = 4, 13`), positivity is certifiably lost at some `x ≤ 1.3 x_h`.
- **S3 (ordering):** the first-loss window `x_c` does not increase with `δ`.
- **S4 (perturbative regime, reported):** outside the horizon (`x < 0.9 x_h`, PD), the ratio of first-order to exact `Δ lnK`. The prediction is a median within 20% of 1.

**What a pass would mean.**
- An off-line zero pair at height `γ₀` is invisible to windows below `x ≈ γ₀/10.8`, and breaks positivity soon after that, even for tiny `δ`. In the window chain, a counterexample to RH looks like **lnK(x) diverging just past `x_h(γ₀)`**.
- Conversely, certified positivity at window `x` rules out off-line zeros up to height about `10.8x`. That is only as strong as known zero verification, and far weaker than it.
- None of this bears on RH beyond the verified range.
