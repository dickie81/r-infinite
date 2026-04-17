# Black Hole Thermodynamics from the Cascade: Status and Roadmap

## What is derived (in Part II=III)

### Bekenstein-Hawking entropy: S = A/d

**Theorem 7.1.** Boundary dominance (Omega_{d-1}/V_d = d) gives V = A/d for a boundary of area A. At d=4: S = A/4.

- Source: Gamma function identity (Part 0, Theorem 3.1)
- Status: **Tier 1.** One line. No physics input.
- The factor 1/4 is 1/d at the observer's dimension, not a numerical coincidence.

### Hawking temperature: T = 1/(8piM)

**Theorem 7.4.** Three steps:
1. S = A/4 (boundary dominance)
2. A = 16piM^2 (Birkhoff's theorem, mathematical consequence of the cascade's Einstein equation via Lovelock)
3. T = (dS/dM)^{-1} = 1/(8piM) (calculus)

- Source: boundary dominance + Lovelock + Birkhoff + chain rule
- Status: **Tier 1.** No QFT on curved spacetime, no Bogoliubov transformations, no semiclassical approximation.
- The first law dM = TdS is output, not input.

### Thermal spectrum: Planckian shape

The cascade's slicing integrand (1-x^2)^{d/2} is Gaussian (Lemma 3.1 of Part II). The decoherence factor D = exp(-Dx^2/4R_eff^2) is Gaussian (Theorem 8.1 of Part II). By the Araki-Woods theorem, Gaussian entanglement across a partition produces a reduced density matrix with geometric eigenvalues p_n = (1-r)r^n, which IS the Bose-Einstein distribution.

Verified numerically: the cascade's Gaussian parameters at d=4 (a = 15/4, b = 7/4) produce eigenvalues matching the geometric series to 4 significant figures (r = 0.2476).

Combined with T = 1/(8piM):

    n(omega) = Gamma(omega) / (exp(omega/T) - 1)

where Gamma(omega) are greybody factors from the wave equation on Schwarzschild (cascade content via Lovelock + Birkhoff).

- Source: Gaussian concentration (Part 0) + decoherence (Part II) + Araki-Woods (mathematical theorem) + Theorem 7.4
- Status: **Tier 2.** The Gaussian-to-thermal step uses a known QI theorem applied to cascade-derived inputs. The greybody factors require solving the wave equation on Schwarzschild, which is standard GR downstream of the cascade's Einstein equation.


## What is computed but needs scrutiny (not yet in the paper)

### Page curve

The Page curve follows from the cascade in 10 steps:

1. Total state is pure (point on S^{d-1}) — Part II
2. S_BH = 4piM^2 — boundary dominance + Birkhoff
3. T = 1/(8piM) — Theorem 7.4
4. Spectrum is Planckian — Araki-Woods
5. Evaporation rate dM/dt = -alpha/M^2 — Stefan-Boltzmann (Part II) + A, T
6. M(t) = (M_0^3 - 3 alpha t)^{1/3} — integrating step 5
7. S_BH(t) = 4piM(t)^2 — step 2 applied to step 6
8. S_rad(t) = min(S_emitted(t), S_BH(t)) — purity (step 1)
9. Page time: t_Page = 0.646 t_evap, where S_rad = S_BH
10. Information recovery: D -> 1 as A -> 0 (Gaussian tail, D > 0 always)

Key numbers:
- Page time: 0.646 t_evap
- Maximum radiation entropy: 0.500 S_0
- Mass at Page time: M_0/sqrt(2) (half the entropy, not half the mass)

### Open issues before inclusion

**Issue 1: Species coefficient.** Step 5 uses Stefan-Boltzmann luminosity L = sigma A T^4. The coefficient involves the number of emitting species (massless fields that can carry radiation). The cascade determines this from the generation structure (Part IVa), but the exact coefficient N_s for BH evaporation has not been computed from cascade content. This affects the evaporation RATE (the timescale) but not the SHAPE of the Page curve.

**Issue 2: Gaussian vs random entanglement.** Step 8 uses Page's prescription S_rad = min(S_emitted, S_BH), which is exact for random states (Haar measure on the total Hilbert space). The cascade's entanglement is Gaussian, not random. For large systems (S_BH >> 1), the Gaussian curve approaches the random-state curve, so the difference is negligible for astrophysical BHs. But the cascade should be able to compute the EXACT curve from its own Gaussian eigenvalue structure, without appealing to Page's random-state approximation. This would give cascade-specific corrections near the Page time.

**Issue 3: Remnant question.** Step 10 assumes the BH fully evaporates (A -> 0). Whether the cascade permits complete evaporation or leaves a Planck-scale remnant is not established. The cascade's finite tower (213 layers) might impose a minimum mass/entropy below which the BH description breaks down. If a remnant exists, the Page curve's endpoint changes: instead of S_rad -> 0, it approaches S_remnant.

**Issue 4: Backreaction.** The evaporation dynamics (steps 5-6) assume the BH radiates into flat space and shrinks quasi-statically. The cascade's geometry (FRW metric on S^3) introduces curvature corrections that modify the late-stage evaporation. For BHs much smaller than the Hubble radius, these corrections are negligible. For cosmological-scale BHs, they matter.


## What is not derived (genuine open problems)

### Greybody factors from cascade geometry

The greybody factors Gamma(omega) modify the Planckian spectrum. They depend on the angular momentum barrier of the Schwarzschild potential. Computing them requires solving the Regge-Wheeler/Zerilli equation, which is standard GR downstream of the cascade's Einstein equation. This is not new cascade content — it's applied PDE work. But it has never been done explicitly within the cascade framework.

### Kerr and charged black holes

The cascade derives S = A/d for any horizon. For Kerr (rotating) or Reissner-Nordstrom (charged) BHs, A depends on mass, angular momentum, and charge. The cascade's Einstein equation admits these solutions (they are unique by the no-hair theorem, another mathematical consequence of the Einstein equation). The temperature and Page curve should follow by the same chain, but with modified A(M,J,Q).

### BTZ cross-check — COMPLETED (Part II=III §7.6, Theorems thm:Gd and thm:btz)

The cascade predicts S = A/d for any d (boundary dominance). Applied at d=3:
- S = A/3
- Matching to standard Bekenstein-Hawking S = A/(4G_d) gives G_d = d/4, so G_3 = 3/4 in cascade units
- Standard BTZ with G_3 = 3/4: r_h² = 6Mℓ², A = 2πℓ√(6M), S = (2πℓ/3)√(6M)
- Cascade Hawking temperature from first law: T = (dS/dM)⁻¹ = r_h/(2πℓ²), matching standard BTZ surface gravity exactly

Verified symbolically in `tools/btz_cross_check.py` (sympy). The cascade's S = A/d formula, applied at d=3, reproduces all known BTZ thermodynamics self-consistently with no free parameters.

Structural implication: G_d = d/4 is a cascade prediction for how Newton's constant scales with dimension. At d=4 this gives the standard G_4 = 1 used in Theorem 7.4 (Hawking temperature at d=4). At d=3 it predicts the dimensionless ratio G_3/G_4 = 3/4.

Remaining stronger result (still open): a *second* cascade-internal derivation of G_d = d/4 via a distinct structural identity, to corroborate Theorem thm:Gd without going through the boundary-dominance + A/(4G_d) match. This is **not** a Kaluza-Klein problem — the cascade explicitly refuses semiclassical reduction over compactified dimensions (Paper I §3.2; Paper II=III §5-6; Paper III §12: the metric is a state property, not an operator on a fixed background). Cascade-native candidates:
  - the proposed discrete cascade action S[φ] = Σ(2α(d))⁻¹(Δφ)² (Paper IVb Remark 4.6) evaluated at layer d, producing a variational derivation of G_d
  - an independent sphere-area identity at layer d equal to d/4
  - a direct computation from the cascade's embedding data at dimension d

Any such route would promote Theorem thm:Gd from "structural matching" to "doubly-derived", tightening the BTZ cross-check from self-consistency to independent corroboration.

### Connection to the cascade's decoherence numbers

The Part 0 Supplement computes the eigenvalue deficit epsilon = 6.11% for the full 213-layer Gram matrix. The cascade retains 93.9% coherence over the full descent. Whether these numbers connect to the BH decoherence structure (e.g., whether the eigenvalue deficit determines the scrambling time or the Page time for cascade-scale BHs) is unexplored.


## Derivation comparison

| Result | Hawking (1975) | Cascade |
|---|---|---|
| S = A/4 | QFT on curved spacetime | Boundary dominance (one line) |
| T = 1/(8piM) | Bogoliubov transformation | dS/dM (three lines) |
| Planckian spectrum | 50 pages of QFT | Gaussian decoherence + Araki-Woods |
| Page curve | Replica wormholes / island formula (2019) | Purity of cascade state + evaporation dynamics |
| Information recovery | Debated for 50 years | D > 0 always (Gaussian tail) |
| First law dM = TdS | Input (BCH 1973) | Output (calculus on S(M)) |
| Greybody factors | Wave equation on Schwarzschild | Same (cascade derives the equation, not the solutions) |

The cascade's route is shorter because it provides S = A/4 geometrically. Hawking had to discover S = A/4 by computing quantum field modes — a tour de force that took 50 pages. The cascade starts where Hawking finished and gets the temperature by differentiation.
