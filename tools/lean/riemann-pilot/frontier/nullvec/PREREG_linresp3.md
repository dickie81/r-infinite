# Pre-registration 19: third order, and larger windows (round 105)

Committed before any third-order term or any window above `x = 12` is computed.

**Third order (the exact expansion, continued).** Let `G = M⁻¹` and let `E = E₁ + E₂ + E₃` be the order-by-order change of `M`. Write `vₙ = Eₙ y` (explicit sums over the nodes of `δ^n` times derivatives of `φ` and of `F` up to third order), and `z = G v₁`. Then:
- `s₁ = −a₁`;
- `s₂ = −a₂ + v₁ᵀGv₁`;
- `s₃ = −yᵀE₃y + 2v₁ᵀGv₂ − Σ_k 2δ_k(φ_k·z)(φ′_k·z)`;
- `Δ₃ ln K = u − u²/2 + u³/3` to third order, with `u = (s₁ + s₂ + s₃)/s`. That is, `(s₁ + s₂ + s₃)/s − (s₁² + 2s₁s₂)/(2s²) + s₁³/(3s³)`.

This reduces to round 104's `Δ₂` when `s₃ = 0` and the `s₁s₂`, `s₁³` terms are dropped.

**A. Third order on the round-104 grid** (`x ∈ [3, 12]`, 226 windows; the true zeros and the `P = 7` zeros). The measure is the correlation of the predicted and actual residuals (4-term smooth fit) and the raw maximum error.
- **PERT** (the remaining 6% is perturbative): third-order correlation `≥ 0.97`, and the raw maximum `|error|` below round 104's second-order 0.080.
- **NONPERT**: third-order correlation `≤ 0.945`, i.e. no gain over the second order.
- Anything in between is reported as partial.

**B. Larger windows** (`x ∈ [12, 30]`, step 0.12, 151 windows; Nyquist 26). The zeros enter individually up to `H = 2500`, so the horizon's `3×` range (`≤ 3·4π·30 = 1131`) is covered. The quantiles are extended to 2500 by `θ(γ̃_k) = (k − 3/2)π`. The actual true and Γ chains are computed with the same kernel (`kzeroside2.py`, `HC = 2500`).
- **HOLDS**: second-order correlation `≥ 0.9` on `[12, 30]`, i.e. the semi-explicit formula survives as the window grows. **DEGRADES** otherwise.
- The third-order correlation on `[12, 30]` is reported with the same PERT and NONPERT thresholds.
