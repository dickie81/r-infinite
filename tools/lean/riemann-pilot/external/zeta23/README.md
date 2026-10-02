# External: zeta23 (round 228)

These files build on zeta23, the Lean formalisation that accompanies Alpöge–Furman (arXiv 2608.13637). zeta23 lives in `anthropics/formal-math`, folder `zeta23`. It is Copyright 2026 Anthropic, PBC and released under the Apache License 2.0; its `Zeta23/FromPNTPlus/` files derive from PrimeNumberTheoremAnd, also Apache 2.0. `build.sh` copies zeta23's `LICENSE` and `NOTICE` next to the files it fetches.

| file | round | content |
|---|---|---|
| `SlogZeta.lean` | 228 | von Mangoldt's bound `|S(t)| ≤ C log t` for Mathlib's `riemannZeta`, in the pilot's terms; the 1ca wall law without `hSlog` |
| `HybridCertificate.lean` | 276 | the rank–trace certificate on zeta23's zero side for coupled vectors `v = w + (ηg)u`, with no RH: the off-line zeros enter through one displayed term |

## What is used from zeta23

`build.sh` compiles 59 zeta23 files at commit `fbdc36b`: the import closures of four results.

| result | zeta23 name | content |
|---|---|---|
| Montgomery–Vaughan | `Zeta23.MV.mv_hilbert` | the weighted Hilbert inequality `∃ C > 0, MVHilbert C` (C = 26) |
| Riemann–von Mangoldt | `Zeta23.RvM.riemannVonMangoldt` | `N(T, 2T) = (T/2π)ℓ₁(T) + O(log T)` and the local count `N(t, t+1] ≤ A₀ log(|t| + 3)`, given the Γ facts |
| the Γ facts | `Zeta23.gammaFacts` | Stirling for `μ(τ) = (1/2π)Re ψ(¼ + iτ/2) − log π/2π` and its integrals |
| the zero side | `Zeta23.ZeroSide` | the abstract block structure `ZeroBlockData` (paper prop:block), the split `Â = P_c + Q_c`, and the rank–trace inequality `RHLinalg.rank_trace_ineq_two` |

`SlogZeta.lean` uses the second and third, through their parts: the argument principle for `Λ = completedRiemannZeta` folded onto the right half-contour (`N_eq_halfContour_completedZeta`), the split `Λ'/Λ = ζ'/ζ + Γ_ℝ'/Γ_ℝ`, Backlund's bound on the horizontals (`backlund_horizontal`), the vertical side at `σ = 2` (`vertical_two`), the Γ side (`gamma_side`) and Stirling (`gammaFacts.stirling`). Montgomery–Vaughan is compiled but not yet used here.

## Building

```
../../build.sh    # the pilot's own files
./build.sh        # zeta23 and this directory
```

`build.sh` does three things:
- It fetches the 59 files at commit `fbdc36b` (Lean v4.33.0-rc2) into `upstream/`. Set `ZETA23` to a clone of `anthropics/formal-math` to use it; otherwise that one commit is fetched. It fetches again when the patch is newer than the last fetch, or when `MODS` names a file that is not in `upstream/`.
- It applies `zeta23_port.patch`, which ports those files to the pilot's toolchain. Four files change, all by Mathlib API drift; the top of the patch lists them. Each changed file carries a note saying so. The nine zero-side files added in round 276 compile unpatched.
- It compiles the zeta23 files (with zeta23's own `relaxedAutoImplicit = false`) and this directory's files into `../../build`, then prints the axioms of the final theorems.

The zeta23 files print their own upstream warnings (deprecations, unused variables); they are compiled unedited apart from the patch. `SlogZeta.lean` and `HybridCertificate.lean` print none.

## SlogZeta.lean (round 228)

- `Ncnt_good`: at a height `T` that is not the ordinate of a zero, the pilot's count `Ncnt zetaOrd T` (zeros with `0 < γ < T`, with multiplicity) equals zeta23's `Ncount 0 T` (zeros with `0 < γ ≤ T`). Both use the multiplicity `(analyticOrderAt ζ ρ).toNat`.
- `Ncount_contour`: for good heights `T₁ < T₂` above Backlund's threshold, `|N(T₁, T₂) − ∫_{T₁}^{T₂} μ| ≤ (|C_B| log T₁ + π + |C_B| log T₂)/π`.
- `int_mu_near`: `|∫_a^b μ − (N₀(b) − N₀(a))| ≤ |C_S|` for `1 ≤ a ≤ b`, from Stirling's `μ(τ) = (1/2π)log(τ/2π) + O(τ⁻²)` and `N₀′(r) = (1/2π)log(r/2π)`.
- `Slog_eventually`, then **`Slog_zeta`**: `∃ C ≥ 0, ∀ t ≥ 14, |S(t)| ≤ C log t`, where `S = N − N₀ − 7/8` is the pilot's `Sz zetaOrd`. For large `t`, sandwich `t` between good heights `T₃ ∈ [t−1, t]` and `T₂ ∈ [t, t+1]`. Below that, `S` is bounded by monotonicity of `N` and `N₀`.
- **`wall_law_zeta_S`**: `wall_law_zeta` (round 5) without the hypothesis `hSlog`. Littlewood's `S₁(T) = O(log T)` (`hS1log`) and the first-zero height stay named inputs.

All axioms are clean.

## HybridCertificate.lean (round 276)

The setting is zeta23's `ZeroBlockData`: distinct zeros `z` in a window, with multiplicities `m_z`, vectors `v_z`, and the reflection `σ : ρ ↦ 1 − ρ̄`. Here `A = Σ_z m_z v_z v_zᵀ`, `c > 0` is the unit (zeta23 takes `c = aL²`), `N = Σ_z m_z`, `s₁ + s₂` counts the distinct on-line zeros, and `R` holds one zero from each off-line pair. Every statement below holds for any such data and any `c > 0`.

- `cert_general`: `4c⁻¹ Re tr A − 2c⁻¹ Re tr P − 4p − ‖c⁻¹A‖²_F ≤ s₁ + s₂`, where `P` is the on-line part of `A` and `p = #R`. This is `rank_trace_ineq_two` applied to zeta23's `blockP c`, `blockQ c`.
- `cert_offline`: `2c⁻¹ Re tr A − ‖c⁻¹A‖²_F + Σ_{z∈R} (4c⁻¹ m_z Re β_z − 4) ≤ s₁ + s₂`, with `β_z = v_z · v_z` (bilinear). There is no hypothesis on the vectors.
- `hybrid_cert`: take `v_z = w_z + (η g_z) u_z`, with `w`, `u`, `g` reflection-symmetric and `η` real. Assume `Σ_k |w_z k|² ≤ c` at each on-line zero; this is zeta23's `hPois`, for the base family `w` only. Then
  `c⁻¹(4A_w + 2A_g) − 2N − ‖c⁻¹A‖²_F + 4c⁻¹ Σ_{z∈R} m_z Re G_z ≤ s₁ + s₂`.
  Here `G_z = 2η g_z (w_z·u_z) + η² g_z² (u_z·u_z)`, `A_w = Re Σ_z m_z (w_z·w_z)` and `A_g = Re Σ_z m_z G_z`.
  `A_w`, `A_g` and `‖A‖_F` are sums over all zeros in the window. The last term is a sum over the off-line pairs only.
- `hybrid_cert_of_offline`: the same bound with the last term replaced by `−4c⁻¹E`, given the displayed input `OFF(E): −E ≤ Σ_{z∈R} m_z Re G_z`.
- `hybrid_cert_of_moments`: splits `OFF` by order in `η`. A first-order input `|Σ_R m Re(g (w·u))| ≤ E₁` and a second-order input `−E₂ ≤ Σ_R m Re(g² (u·u))` give the bound with `−c⁻¹(8|η|E₁ + 4η²E₂)`.
- `hybrid_cert_of_no_offline`: if `R = ∅`, the bound holds with `E = 0`.
- `hybrid_cert_eta_zero`: at `η = 0`, the bound is `4c⁻¹A_w − 2N − ‖c⁻¹A‖²_F ≤ s₁ + s₂`. That is the inequality of zeta23's `Assembly.zeroside_rank_core`, `4 tr Â − 2N(I′) − ‖Â‖²_F ≤ r`.

The normalisation is imposed on `w` alone. If it were imposed on `v`, it would need a pointwise bound on `g` at each on-line zero.

All axioms are clean.
