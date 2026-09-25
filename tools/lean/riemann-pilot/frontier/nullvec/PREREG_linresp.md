# Pre-registration 18: the semi-explicit Hamiltonian by response theory (round 104)

Committed before any response quantity is computed.

**Object.** On the zero side, `K_a(0,0) = (2a)² · s`, with `s = e₀ᵀM⁻¹e₀`, `M = ΦᵀΦ`, and `Φ`'s rows `φ(γ)` taken at the zeros (plus the fixed smooth tail above 1000; `kzeroside2.py`).

**Base.** The smooth quantiles `γ̃_k` (the pure-Γ chain, which has no wiggles; round 91).

**Arithmetic input.** The displacements `δ_k = γ_k − γ̃_k`, i.e. `S(t)` read at the zeros.

**Expansion (exact algebra, no fitting).** Write `y = M⁻¹e₀` and `F_k = φ(γ̃_k)·y` (the base ground state's transform at the node), with `F′_k`, `F″_k` its γ-derivatives. Let

- `a₁ = Σ 2F_kF′_k δ_k`,
- `a₂ = Σ (F_kF″_k + F′_k²) δ_k²`,
- `v₁ = Σ δ_k (φ′_kF_k + φ_kF′_k)`.

Then

- `Δ₁ ln K = −a₁/s`,
- `Δ₂ ln K = Δ₁ − a₂/s + v₁ᵀM⁻¹v₁/s − a₁²/(2s²)`.

Every factor comes from the Γ base chain; the arithmetic enters only through `δ`. This is the proposed semi-explicit Hamiltonian:

`ln K = ln K_Γ + Δ[w_x; S]`, and `H = d/da` of that.

**Physics expected.** Below the edge the base ground state nearly vanishes at the nodes (balayage), so `F_k ≈ 0`. There the first-order weight `F_kF′_k` is small and the response is quadratic (`F′²δ²` minus re-optimisation, `v₁ᵀM⁻¹v₁`). Above the edge `F_k ≠ 0` and the first order dominates. This would explain why the window reads just beyond its edge.

**Test.** Same grid as rounds 95–103 (`x ∈ [3, 12]`, 226 windows). Compare the predictions with the actual `ln K_true − ln K_Γ` (round 95 chains), after the 4-term smooth fit. Also run the `P = 7` displacements against its actual chain, and report the tones of the predicted residual.

| outcome | condition |
|---|---|
| **LR2 pass** (the semi-explicit Hamiltonian holds) | second-order prediction correlates `≥ 0.9` with the actual residual, rms ratio in `[0.7, 1.3]` |
| **Partial** (a third order or non-perturbative remainder is needed) | correlation in `[0.5, 0.9)` |
| **Fail** (the expansion does not converge in `δ`) | correlation `< 0.5` |

The first-order correlation is also reported; I expect it to be clearly below the second-order one.
