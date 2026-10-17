# The λ₂ lower bound, attacked directly (round 167)

## 0. What a "lower bound on λ₂" can mean

`λ₁(a) ≤ λ₂(a)` are the two lowest eigenvalues of Weil's form `Q` on real probes supported in
`[−a, a]`. Three different statements go by the name "lower bound on λ₂". They have very
different strength.

| statement | strength | where recorded |
|---|---|---|
| (P) `λ₂(a) > 0` for every `a` | RH-strength: `Q` has at most one negative direction on every window | round 152, obstruction 3 (acknowledged) |
| (N) `λ₂(a) ≥ −C e^{2θa}` for every `a`, with `θ < ½` | forces a zero-free strip `Re ρ ≤ ½ + θ` (§2), open since Riemann | new here (paper sketch) |
| (G) `λ₂(a) > λ₁(a)` (simplicity) | not RH-strength; CCM's open step (i) | rounds 48–52 and 148–151 (acknowledged) |

- **The trivial case of (N).** `θ = ½` is the prime-side floor
  `λ₁ ≥ ψ(¼) − log π − 2Σ_{n≤e^{2a}}Λ(n)n^{−½} − (pole)`, already in Lean
  (`weilQg_odd_ge`, `lam_bdd`).
- **What survives.** Every "for all `a`" absolute bound between the trivial floor and zero is at
  least as hard as a zero-free strip. So the only unconditional absolute bounds available are on
  **finite ranges of `a`**.
- **The target.** §1 gives the strongest such bound I could build: near-exact positivity up to
  `δ = 2a ≈ 4.2`, about twice the pilot's certified range (`δ ≤ 2.07`, round 47).

## 1. Theorem (near-positivity to δ = 4.2047)

**Theorem NP.** Assume the Platt–Trudgian verification of RH to height `H₀ = 3·10¹²`: every zero
`ρ = ½ + iγ` with `0 < γ ≤ H₀` has real part `½`. Then for every `0 < a ≤ a* := ½log 67 − 10⁻⁶`
(`δ* = 4.20469`) and every real probe `g` supported in `[−a, a]`:

  `Q(g) ≥ −10^{−18985} ‖g‖²`.

Hence `λ₂(a) ≥ λ₁(a) ≥ −10^{−18985}` on that range, in both parity sectors.

For comparison:
- the trivial floor is about `−28` at `a*`;
- the true `λ₁(a*)` is about `e^{−4πe^{2a*}} = e^{−842} ≈ 10^{−366}` (it would be positive under RH).

So the bound is "uselessly low" against the truth, but it improves the floor by about 19 000
orders of magnitude.

### Proof

Throughout, `F = ĝ`, `G(t) = F(t)F(−t)` (so `G = |F|²` on `ℝ`), and `σ_a(t) = arch(t) − D_a(t)`, where:
- `arch(t) = Re ψ(¼ + it/2) − log π`;
- `D_a(t) = 2Σ_{n≤e^{2a}} Λ(n)n^{−½} cos(t log n)`.

The pilot's form is, exactly,

  `Q(g) = 2G(i/2) + (1/2π) ∫ G σ_a dt`.     (1)

This is round 50's symbol, read in frequency.

1. **The cutoff.**
   - Let `m ≥ 1`, `α > 0`, and `K(y) = c·(sin αy / αy)^{2m}` with `∫K = 1`. Then `K ≥ 0` is
     even and entire, and `K̂` is supported in `[−2mα, 2mα] = [−τ/2, τ/2]`.
   - Put `w = 1_{[−T₂, T₂]} * K`. Then:
     - `0 ≤ w ≤ 1` on `ℝ`;
     - `w` is even and entire, of exponential type `τ/2`;
     - `|K(x + iη)| ≤ c e^{τ|η|/2} (α|x|)^{−2m}`.
2. **The explicit formula for `h = Gw`.**
   - `ȟ` is supported in `[−(2a + τ/2), 2a + τ/2]`.
   - Choose `τ/2 < d(a) := log n₊ − 2a`, where `n₊` is the first prime power above `e^{2a}`.
     Then the prime sum in Weil's explicit formula for `h` contains exactly the `n ≤ e^{2a}`
     terms, so
     `Σ_ρ h(t_ρ) = 2h(i/2) + (1/2π)∫ h σ_a dt`.
   - `h` is analytic and rapidly decaying in the strip `|Im t| ≤ ½ + ε`, so it is an admissible
     test function (pilot, round 156, `WeilExplicit` for strip test functions).
3. **The exact split.** Subtracting from (1):

   `Q(g) = Σ_ρ h(t_ρ) + 2G(i/2)(1 − w(i/2)) + (1/2π)∫ G(1 − w) σ_a dt`.     (2)

4. **Signs.**
   - **Zeros with `|γ| ≤ H₀`.** They are on the line, so they contribute `|F(γ)|²w(γ) ≥ 0`.
     `ζ` has no zeros in `(0, 1)`, so no `t_ρ` is imaginary.
   - **The high band.** `arch` is increasing in `|t|` and `D_a ≤ A_a := 2Σ_{n≤e^{2a}} Λ(n)/√n`.
     So `σ_a ≥ 0` for `|t| ≥ T₁`, where `arch(T₁) = A_a`. There `1 − w ≥ 0` as well.
5. **Errors.** Three terms can be negative. Each uses `|F(z)F(−z)| ≤ 2(e^a − 1)‖g‖²` for
   `|Im z| ≤ ½` (Cauchy–Schwarz).
   - **E1, the low band `|t| < T₁`.** Here `1 − w(t) ≤ ∫_{|u|>T₂−T₁} K`, and
     `σ_a^− ≤ A_a + 5.4`.
   - **E2, the pole.** `|1 − w(i/2)| = |∫_{|y|>T₂} K(i/2 − y) dy|`.
   - **E3, zeros with `|γ| > H₀`**, on the line or not.
     - `|w(x + iη)| ≤ ∫_{|u| ≥ |x| − T₂} |K(u + iη)| du`.
     - At most `log T + 10` zeros lie in `[T, T + 1]` (Trudgian's bound for `S(T)`, generous).
     - Each orbit has at most 4 members.
   - All three are `(2c/α)(αX)^{1−2m}/(2m − 1)` times harmless factors, with `X = T₂ − T₁`,
     `T₂` or `H₀ − T₂`. For the normalisation, `c ≤ (α/2)e^{2m/5}`, using
     `sin u/u ≥ e^{−u²/5}` on `|u| ≤ 1`.
6. **Parameters** (`near_pos_constants.py`, 50 digits).

   | quantity | value |
   |---|---|
   | `A_{a*}` | `26.671` |
   | `T₁` | `2.4057·10¹²` |
   | `T₂` | `(T₁ + H₀)/2` |
   | `X` | `2.97·10¹¹` |
   | `d` | `2·10⁻⁶` |
   | `τ` | `d/2` |
   | `m` | `27330` (`≈ τX/4e`) |
   | `E1` | `≤ 10^{−18994}` |
   | `E2` | `≤ 10^{−71402}` |
   | `E3` | `≤ 10^{−18985}` |

7. **All `a ≤ a*` at once.** `λ₁` is nonincreasing in `a` (`lam_antitone`, and
   `lamO_antitone` for the odd sector). So the bound at `a*` covers every smaller support,
   including those near a prime-power jump, where `d(a)` would be tiny. ∎

**Why `a*` is where it is.** The next prime power, 67, raises `A_a` by `2 log 67/√67 = 1.03`.
That moves `T₁` to `6.7·10¹²`, past `H₀`. Each further step in `δ` of `O(1)` needs the verification height
multiplied by roughly `e^{2e^{δ/2}}`: `δ_max ≈ 2 log(log H₀ / 4)` grows only doubly
logarithmically in `H₀`.

**Why this is not exact positivity.** `w` is entire, so `1 − w` cannot vanish on `[−T₁, T₁]`.
Absorbing E1 into the on-line zero sum would need a sampling inequality:
`Σ_{|γ|≤T₂} |F(γ)|² + ∫_{|t|>T₂} |F|² ≥ M⁻¹ ‖F‖²` on the Paley–Wiener space `PW_a`, with
`M⁻¹ ≫ 10^{−18985}`.
- **Why it should hold.** The zeros exceed the Nyquist density beyond `T* ≈ 2πe·e^{2a}`. The
  true constant is on the `λ₁` scale, `10^{−366}`, so the slack is enormous.
- **Why it is not proved here.** A rigorous proof needs local zero-spacing information up to
  `T₁` (max gap below `π/a`). Trudgian's `S(T)` bound only gives gaps below about 3, which is
  not enough. The required data (zeros to `2.4·10¹²`) are beyond this session.

This is the one step between Theorem NP and **unconditional Weil positivity to δ = 4.2**.

## 2. The barrier for "every a" (paper sketch)

**Proposition.** Suppose `ζ` has a zero `ρ₀ = ½ + η₀ + iγ₀` with `η₀ > 0`, and suppose
`η₀ = max η` is attained. Then `λ₁(a) ≤ −c e^{2η₀a}` along a sequence `a → ∞`.

**Consequence.** A bound `λ₁(a) ≥ −C e^{2θa}` for all `a`, and a fortiori the same bound for
`λ₂`, implies `Re ρ ≤ ½ + θ` for all zeros.

**Sketch.** Round 131's twin probes `g_λ = g₀(· − λ) + g₀(· + λ)` have transform
`2cos(λz)ĝ₀(z)` and `‖g_λ‖² = 2‖g₀‖²`.
- The quadruple of `ρ₀` contributes `Re(4cos²(λt₀)ĝ₀(t₀)²) ~ e^{2λη₀}·(oscillating sign)`.
- Every other term is `O(e^{2λη}Σ|ĝ₀(t_ρ)|²)` with `η < η₀`, or bounded (on-line zeros).
- The weighted average of C2–C5 (round 131) then picks `λ` in each window `[Λ, 2Λ]` where
  `Q(g_λ) ≤ −c e^{2Λη₀}`.

What is not formal: the "max attained" hypothesis. With infinitely many off-line zeros, take any
`η' < sup η`.

**Numerical illustration** (DH, round 165 data, `K = 120`). Past its first failure,
`λ₁^{DH}` runs `−8·10⁻³⁰` (a = 1.725), `−4.8·10⁻¹⁸` (1.775), `−2.5·10⁻⁷` (1.8), `−0.71` (2.0).
A second negative eigenvalue (`−4·10⁻¹⁷`) appears at a = 2.0, from the next off-line zero. The
`e^{2aη₀}` regime needs larger `a` than was computed.

So every absolute λ₂ bound valid for **all** `a` is either the trivial floor (`θ = ½`) or at least
a zero-free strip. **Finite-range bounds (§1) are the only unconditional absolute improvements**,
and their reach is doubly logarithmic in the verification height.

## 3. What remains for the comparative bound (G)

- Theorem NP gives nothing for `λ₂ − λ₁`.
- The reductions are formal (`not_simple_iff_secular`: simplicity fails iff `μ₂(Q₀) = λ₁(Q)`).
- The literature and the pilot agree that the obstruction is the same large-support spectral
  asymptotics (CCM step (i)).
- No new handle on (G) was found this round.

## Check 4

- **Acknowledged.**
  - (P) is RH-strength (round 152).
  - (G) and its reductions (rounds 48–52, 148–151).
  - The threshold `T₁ = 2π e^{A_δ}` is Zhu's (round 47 §3).
  - The explicit formula, Platt–Trudgian, and Trudgian's `S(T)` bound.
- **New here, as far as checked.**
  - The band-limited split (2), which turns RH verification into near-positivity with
    super-exponentially small error.
  - Theorem NP with its constants.
  - The quantitative barrier for (N), a sketch.
  - The identification of the single missing step to exact positivity: a sampling inequality
    at `M⁻¹ ≫ 10^{−18985}`.
- **Literature check** (web survey; quotes read from arXiv pages):
  - Platt–Trudgian (arXiv:2004.09765) abstract: "all zeroes β + iγ of the Riemann zeta-function with 0<γ≤3·10^12 have β = 1/2".
  - The closest analogue found is for Li coefficients, not for windowed Weil forms. Voros (arXiv:2204.01036 §2.2.2) quotes Oesterlé (unpublished, 2000): "Re ρ = 1/2 holds up to a height T0 ⟹ λn > 0 as long as n < T0^2".
  - Zhu (arXiv:2608.24827) uses the Platt–Trudgian zeros only for trial vectors (upper bounds). His positivity proof is prime-side, to support `[−0.8, 0.8]`.
  - No paper was found stating "RH verified to height H ⇒ `Q ≥ −ε` (or `≥ 0`) on windows of support about `2 log log H`". Novelty is **not** established, only not refuted.

**Bearing on RH:** none. §2 shows that for-all-`a` improvements are zero-free-strip-hard, and
§1's range grows only doubly logarithmically in the verification height.
