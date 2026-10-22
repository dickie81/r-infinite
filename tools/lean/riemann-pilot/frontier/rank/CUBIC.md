# The cubic route: the theta component of its dual, and a fixed point

Side-branch note, 2026-10-22, on branch `claude/latest-commit-branch-ik1pj3`. It follows `ORDER-RANK.md` in this directory. It is not a README round, and it adds no Lean. Every number below comes from the gate scripts in this directory (section 7).

**The question.** The owner's instruction: "Keep exploring the cubic route". `ORDER-RANK.md` left one family on the companion's route that could go below `7/8`: the cubic family `A_Z(u) = Σ_𝔞 μ(𝔞)(u/𝔞)₃W(N𝔞/Z)` over `ℚ(ω)`. Its extraction gives `θ₃(σ) = (5 + 2σ)/6`, below `7/8` for `σ < 1/8`. The Missing Prop recorded there is the family's dual mean square at some `σ < 1/8`.

**Summary.**
1. **The dual numerically.** In the regime the route needs (rows `N(k) ≤ H` with `H` up to `Z`), the cubic family's dual mean square is at diagonal size for `Z` up to `8·10⁴` (section 1). Without the Möbius weight the excess is Heath-Brown's `(HZ)^{2/3}` term, with the predicted growth in `Z` and in `H`.
2. **The excess.** It is a single vector, the cubic theta component `c·conj(G₃(k))·N(k)^{−1/6}·m_w(k; Z)` with `m_w(k; Z) = Σ_{N(n)≤Z, (n,k)=1} w(n)N(n)^{−1/6}`. The constant `c ≈ 0.59` is one real number for the four weights and four `Z` fitted. Removing the component leaves at most the diagonal (section 2). This is Dunn–Radziwiłł's correction term, measured.
3. **The Möbius rows.** They contain the same component, with the Möbius mass in place of `m_w`: projection coefficient `0.990 ± 0.049`, about 20 standard errors from `0` (section 3).
4. **A fixed point** (section 4; gates O6–O8, exact arithmetic).
   - The component's share of the dual mean square is of order `H^{2/3}·|Σ_{N(n)≤Z} μ(n)N(n)^{−1/6}|²`. That is a Möbius sum of `ζ_K`, the quantity the family is built to bound.
   - Bounding the component from an input half-plane `Re s > θ₀` needs `σ ≥ 3θ₀ − 5/2`, and the extraction then returns exactly `θ₀`.
   - At `θ₀ = 1` (no input) this is `σ ≥ 1/2`, Heath-Brown's barrier: the generic barrier is this component at the trivial bound for the Möbius sum.
5. **Why the sextic family escapes.** Its absorbed dual coefficient `c(n)α(n)G₂(n)·conj(G₃(n))` has no Möbius factor. Its cubic theta component carries the mass of a Grössencharacter twist, which convexity bounds with no input (section 3). *(`PAIRING.md`, section 3: true of the cubic theta component. The sextic dual's own sextic theta component keeps the Möbius sum, and the absorbed energy bound applied to it is the extraction's `θ₆(σ)`.)*
6. **What is left of the cubic route.** A treatment of the dual that bounds the component without an input half-plane: in effect, a proof of `|Σ μ(n)N(n)^{−1/6}| ≪ Z^{1+ε}H^{−1/3}`, the half-plane `θ₃(σ)` itself, made while bounding the rest. `ORDER-RANK.md`'s second attack note took the bias-free numerics as evidence of room. That signal is circular (CLAUDE.md Check 9(c), section 6).

## 1. The regime the route needs

The dual is the one of `ORDER-RANK.md` section 4, at the block `B = F = 1`:
- rows `k` with `0 < N(k) ≤ H = Z^{1−σ}`;
- columns: the squarefree primary `n` prime to `6`, with coefficient `μ(n)G₃(n)` and the cubic symbol `χ_n = (·/n)₃`;
- the rows' total `S = Σ_k |Σ_n μ(n)G₃(n)·conj(χ_n(k))|²` must be `≪ Z^{2+ε}`.

Going below `7/8` needs this at some `H > Z^{7/8}`.

Since `|μ(n)G₃(n)| = 1`, the coefficients' squared norm is the number of moduli, about `Z`, and the target asks for an operator norm `≤ Z^{1+ε}`. Heath-Brown's cubic large sieve, `H + Z + (HZ)^{2/3}`, meets that iff `H ≤ Z^{1/2}`: `σ ≥ 1/2` and `θ₃ = 1`.

`critical.py` computes `S` and its exact diagonal `Σ_k Σ_{(n,k)=1} |w(n)|²` for:
- the cubic coefficient `w·G₃` against `conj(χ_n(k))` (`d = 3`);
- the sextic coefficient `w·G₆` against the conjugate sextic symbol (`d = 6`; with `w = μ` this is the sextic family's dual, the companion's case);
- the weights `w = 1`, `μ` and the indicator of primes.

The run covers every nonzero `k` with `N(k) ≤ H`, for `Z = 5·10³, 10⁴, 2·10⁴, 4·10⁴, 8·10⁴` and `H = Z^{3/4}, Z^{7/8}, Z/2, Z`. At the top that is 22589 moduli and 290238 frequencies.

`(S − diag)/diag`:

| `Z` | cubic, `μ`, `H = Z^{7/8}` | cubic, `μ`, `H = Z` | sextic, `μ`, `H = Z` | cubic, `w = 1`, `H = Z` |
|---|---|---|---|---|
| `5·10³` | `−0.059` | `−0.043` | `−0.002` | `+3.09` |
| `10⁴` | `−0.045` | `−0.015` | `−0.010` | `+4.02` |
| `2·10⁴` | `−0.031` | `−0.018` | `−0.010` | `+5.09` |
| `4·10⁴` | `−0.000` | `−0.003` | `−0.005` | `+6.48` |
| `8·10⁴` | `−0.005` | `−0.009` | `+0.001` | `+8.24` |

The gates on these numbers:
- **C1.** With `μ` the cubic dual is at diagonal size. `|S − diag|/diag` is at most `0.0895` at every `Z` and `H` computed (the gate allows `0.10`), and at most `0.0091` at `Z = 8·10⁴` for `H ≥ Z^{7/8}` (the gate allows `0.02`).
- **C2.** The same for the sextic dual: at most `0.037` (the gate allows `0.10`).
- **C3.** Without `μ`, the excess at `H = Z` grows by `1.302, 1.266, 1.273, 1.273` per doubling of `Z`, against `2^{1/3} = 1.260`. Relative to the diagonal `HZ`, that is Heath-Brown's `(HZ)^{2/3}·Z` at `H = Z`.
- **C4.** At fixed `Z` the excess grows like `H^{0.675…0.692}` (predicted `H^{2/3}`).

## 2. The excess is the cubic theta component

`theta.py` takes the rows at the squarefree primary `k`, which are the rows of Dunn–Radziwiłł's corrected sieve (below). It fits the predicted component `c·u(k)·N(k)^{−1/6}·m_w(k; Z)` with one complex constant `c`, fitted on `w = 1`. Five candidates for the unimodular `u(k)` are tried: `G₃(k)`, `conj(G₃(k))`, `G₃(k)²`, `conj(G₃(k))²` and `1`.

| `Z` | `c` (fitted on `w = 1`; on primes) | share of the `w = 1` excess removed by `conj(G₃(k))`; by the best other | `(S − diag)/diag` after removal: `w = 1`, primes |
|---|---|---|---|
| `10⁴` | `0.5958`; `0.5980` | `1.056`; `0.031` | `−0.234`, `−0.276` |
| `2·10⁴` | `0.5935`; `0.5929` | `1.044`; `0.023` | `−0.230`, `−0.241` |
| `4·10⁴` | `0.5938`; `0.5941` | `1.032`; `0.018` | `−0.215`, `−0.224` |
| `8·10⁴` | `0.5896`; `0.5895` | `1.023`; `0.014` | `−0.194`, `−0.220` |

(Last column at `H = Z`. At every `H`, for `w = 1`, primes and the sign of section 3, the values lie between `−0.54` and `−0.03`.)

- **T1.** Of the five candidates, only `u(k) = conj(G₃(k))` carries the excess. The fit removes all of it; the share is above `1` because the remainder is below the diagonal.
- **T2.** `c` is real (`|Im c| ≤ 0.002`). It is the same for `w = 1` and for primes, and it moves by `0.006` across `Z`.
- **T3.** After removal, the rows for `w = 1`, primes and the multiplicative sign of section 3 are at or below the diagonal at every `Z` and `H`.

**Reading.**
- `conj(G₃(k))` is the cubic theta function's coefficient at squarefree `k`. Chinta–Friedberg–Hoffstein, section 2, give it at a prime: "τ (3) 1 (p) =G(3) 2 (1,p )", in the text extraction. `G⁽³⁾₂` is the Gauss sum of the squared symbol, which is `conj(G₃(p))` since `χ(−1) = 1`. The extraction continues "=G(3) 1 (1,p )"; an overline there is probably lost.
- The fit holds at composite `k` too, which is most rows. So the coefficient at squarefree `k` is `conj(G₃(k))`, cross terms included.
- `N(k)^{−1/6}` and `Σ w(n)N(n)^{−1/6}` are the weights of the theta residue at Patterson's exponent `5/6 = 1 − 1/6`.

This is the correction term of Dunn–Radziwiłł (A. Dunn and M. Radziwiłł, "Bias in cubic Gauss sums: Patterson's conjecture", Ann. of Math. 200 (2024), arXiv:2109.07463).
- Their abstract: "we show that Heath-Brown's cubic large sieve is sharp up to factors of X^{o(1)} under the Generalized Riemann Hypothesis". Also: "An important ingredient in our proof is a dispersion estimate for cubic Gauss sums. It can be interpreted as a cubic large sieve with correction by a non-trivial asymptotic main term."
- Their Proposition 9.1 subtracts, from each row `Σ_{(b,a)=1} β_b g̃(b)(a/b)₃`, the term `(2π)^{2/3}/(3Γ(2/3))·g̃(a)/N(a)^{1/6}·Σ_{(b,a)=1} β_b/N(b)^{1/6}`. It assumes `β ∈ C_η(B, w)`, their Definition 3.1, which asks for:
  - `|β_b| ≤ 1`, with support on squarefree `w`-rough `b ≡ 1 (mod 3)` and `N(b) ≍ B`;
  - cancellation up to `(B/N(u))^{1/2+η+ε}` against the twists `(b/|b|)^ℓ N(b)^{it}(k/b)₃`, "provided that ℓ ≠ 0, or if ℓ = 0, then provided that k ≠" a cube. (The extraction drops the cube symbol.)

  The principal twist is exempt, so the hypothesis does not bound a weight's mass. Their Lemmas 6.1–6.2 put their own sequences in the class under GRH ("Assume the Generalized Riemann Hypothesis for the Dedekind zeta function attached to Q(ω) twisted by Größencharaktern").
- Their section 1.4 says the correction "allows us to beat the exponent (AB)^{2/3}, albeit only for sequences that have substantial cancellations against all non-principal cubic characters". It adds: "This suggests that in order to beat the cubic large sieve, the correction term alone is not enough; we really need to know additional information about the sequence β_b."
- Their sharpness example: "One example establishing optimality in the range A = B^{1−ε} (for any given small ε > 0) is β_b = g̃(b)." That is the `w = 1` row here.

Not reconciled with their statement:
- the constant: `c ≈ 0.59` here against `(2π)^{2/3}/(3Γ(2/3)) = 0.838` there. This note uses a sharp cutoff and excludes the prime `2` from the moduli; they use a smooth weight `V`.
- the direction: `conj(G₃(k))` here against their `g̃(a)`. Their symbol and additive-character conventions are not checked against `composite.py`'s.

## 3. The Möbius rows carry the Möbius sum

**The Möbius weight.** Its mass `m_μ(k; Z) = Σ_{(n,k)=1} μ(n)N(n)^{−1/6}` is small at these `Z`. In total, `Σ_{N(n)≤Z} μ(n)N(n)^{−1/6}` is `−47.2, −43.7, −55.1, −48.1` at `Z = 10⁴ … 8·10⁴`, against `730.7 … 4128.6` for `w = 1`. The predicted component is accordingly `0.038`–`0.004` of the diagonal at `H = Z`.

Its presence is measured by the projection coefficient `Re⟨X, T⟩/|X|²` of the Möbius rows `T` on the predicted vector `X`, with `c` from the `w = 1` fit:

| `Z` | `H = Z^{3/4}` | `Z^{7/8}` | `Z/2` | `Z` | component/diag at `H = Z` |
|---|---|---|---|---|---|
| `10⁴` | `0.719` | `0.904` | `1.046` | `1.047` | `0.0376` |
| `2·10⁴` | `0.811` | `1.027` | `1.026` | `0.968` | `0.0170` |
| `4·10⁴` | `0.901` | `1.096` | `0.925` | `0.977` | `0.0105` |
| `8·10⁴` | `1.027` | `0.919` | `0.963` | `0.965` | `0.0044` |

**T4.** Pooled at `H = Z` over the four `Z`, weighting each by rows × component/diag (the inverse variance of a projection on a small component), the coefficient is `0.990 ± 0.049`, about 20 standard errors from `0`. The Möbius rows contain the theta component with the Möbius mass, at the predicted size.

**T5. A multiplicative sign with a mass.** The weight is `w(n) = Π_{π|n} ε(π)`, with `ε(π) = −1` iff `N(π) ≡ 7 (mod 8)`. It changes sign like `μ`, and its mass is of order `Z^{5/6}(log Z)^{−1/2}` (`165.6 … 861.5`). Its projections at `H ≥ Z^{7/8}` are `0.957`–`1.023`.

So the component is linear in the weight's mass over masses from `−55` to `4129`, for `1`, primes, a multiplicative sign and `μ`.

**The sextic family, for contrast.**
- Its dual row `Σ_n μ(n)G₆(n)·conj(χ⁽⁶⁾_n(k))` is, by A3 of `ORDER-RANK.md` and `conj(χ⁽⁶⁾) = χ⁽²⁾χ⁽³⁾`, the conjugate of `Σ_n b_n G₃(n)·conj(χ_n(k))`. Here `b_n = conj(β_n)·χ⁽²⁾_n(k)` and `β_n = μ(n)G₆(n)/conj(G₃(n)) = c(n)α(n)G₂(n)`.
- So its cubic theta component has the mass `Σ_{(n,k)=1} b_n N(n)^{−1/6}`, with no Möbius factor. The weight `ᾱ·ψ_k`, with `ψ_k` of finite order, has a nontrivial infinity type. Its mass is therefore a partial sum of an entire `L(s + 1/6, ᾱψ_k)/L(2s + 1/3, ᾱ²ψ_k²)`.
- Convexity bounds that mass by about `Z^{1/3+ε}N(k)^{1/4+ε}`, so the component is at most about `Z^{2/3}H^{7/6} ≤ Z^{11/6}` for `H ≤ Z`, with no input half-plane. (A sketch at the level of the mass rule; the ray-class conductor of `ψ_k` and the conventions are not tracked.)
- **T6.** Numerically this component is present (pooled projection `1.271 ± 0.181`, within 3 standard errors of 1). It is `0.05`–`0.10` of the cubic family's Möbius component at `H = Z`.

## 4. The fixed point

The component's total in the cubic family's dual is `c²Σ_{k≤H} N(k)^{−1/3}|m_μ(k; Z)|²`. Here `Σ_{N(k)≤H} N(k)^{−1/3} ≍ H^{2/3}`, and `m_μ(k; Z)` is the Möbius sum `M_{1/6}(Z) = Σ_{N(n)≤Z} μ(n)N(n)^{−1/6}` restricted to `(n, k) = 1`. So the total is of order `H^{2/3}|M_{1/6}(Z)|²`.

Suppose a half-plane `Re s > θ₀` is known for `ζ_K = ζ·L(·, χ₋₃)`. Then `M_{1/6}(Z) ≪ Z^{θ₀ − 1/6 + ε}`, and the component is at most `H^{2/3}Z^{2θ₀ − 1/3 + ε}`. This is within the target `Z^{2+ε}` iff `σ ≥ 3θ₀ − 5/2`. At that `σ` the extraction returns `θ₃(3θ₀ − 5/2) = θ₀` exactly, for `θ₀ ≥ 5/6`. **Gate O7** checks this on 207 values in `[5/6, 1]`. For example, Sang's `0.8748867` needs `σ ≥ 0.1246601` and returns `0.8748867`. Through this component, the route returns the half-plane it is given.

- **O8.** At `θ₀ = 1`, the trivial bound for the Möbius sum, the component's exponent is `(2/3)(2 − σ) + 1` for every `σ`. That is Heath-Brown's `(HZ)^{2/3}·Z`, and `σ ≥ 1/2`. So the generic barrier recorded in `ORDER-RANK.md` is this component at `θ₀ = 1`. The measured `w = 1` rows (C3, C4, T1) are the same component at the largest mass.
- **O6.** A saving `Z^{−δ}` on Heath-Brown's term gives `θ₃ = max(5/6, 1 − δ/2)`. It goes below `7/8` iff `δ > 1/4` and below Sang's record iff `δ > 0.2502266`. That saving is the component at `θ₀ = 1 − δ/2`. So a structured cubic large sieve for `μG₃` that beats `7/8` contains a Möbius bound beyond `7/8`.

**Scope** (CLAUDE.md Check 9(a)). The fixed point concerns treatments that isolate the cubic theta component and bound it through the Möbius sum:
- the cubic theta's summation formula (Dunn–Radziwiłł's Proposition 8.1);
- their corrected large sieve (Proposition 9.1);
- the plain cubic large sieve, for which the component is the extremal direction.

A treatment that bounds the whole dual mean square without isolating the component also bounds the component, since T4's remainder is orthogonal to it within `±0.05`. So it proves `M_{1/6}(Z) ≪ Z^{1+ε}H^{−1/3}`, the half-plane `θ₃(σ)`, along the way. That is not excluded here; it is a direct proof of the half-plane, with the family as scaffolding.

The component's form for the Möbius weight is measured (T4, T5) for `Z ≤ 8·10⁴`. It is also the correction term of Dunn–Radziwiłł's Proposition 9.1, whose class `C_η(B, w)` exempts the principal twist, so its hypothesis does not assume the Möbius mass small. Three limits apply:
- `μ` is not `w`-rough.
- Its remainder bound saves only `w^{9/10}`, with `w > (log X)^{10}`, on one copy of `(AB)^{2/3}B`, and a power `ρ(ε) ∈ (0, 1/10000)` on another.
- It has further terms, such as `B^{29/12}A^{−1/12}`, that exceed `B²` near `A = B`.

So the proposition neither applies to `μ` as stated nor bounds the cubic route's remainder. The form is used here as a structural statement supported by the numerics, not as a theorem.

The same correspondence appears in Hamdar's first moment of the cubic family (arXiv:2509.06152), quoted in the register (round 506's bullet): "a main term of the principal sum which comes from cubes, and the contribution from infinitely many residues of Dirichlet series of cubic Gauss sums to the dual sum". Here the family's cubes `u = b³` carry `Σ_{(n,b)=1} μ(n)W(N(n)/Z)`, the extraction's sum. The dual's theta residues carry `Σ_{(n,k)=1} μ(n)N(n)^{−1/6}`.

## 5. The sextic theta at fourth powers, and the carriers

Chinta–Friedberg–Hoffstein ("Double Dirichlet series and theta functions", 2011, `chinta.ccny.cuny.edu/publ/patterson.pdf`), section 2, give the Hecke relations of the theta function on the `k`-fold cover of GL₂. The text extraction flattens the indices: "τ (k) 1 (mpi) =G(k) i+1(m,p )τ (k) 1 (mpk−2−i), (2.5) valid for k≥ 2, p a prime, 0≤i≤k− 2, and (m,p ) = 1."
- **At `k = 6`, `i = 4`.** This reads `τ⁽⁶⁾(mp⁴) = G⁽⁶⁾₅(m, p)·τ⁽⁶⁾(m)`, so `τ⁽⁶⁾(p⁴) = G⁽⁶⁾₅(1, p)`: the Gauss sum of the fifth power of the sextic symbol, `conj(G₆(p))` up to `χ(−1)` and conventions.
- **The cubic dual.** By A4 of `ORDER-RANK.md`, `μG₃ = c·α·conj(G₆)·conj(G₂)`. So at primes the cubic dual's coefficient is the GL₂ sextic theta's coefficient at `p⁴`, up to `α`, `G₂` and a unit.
- **Their Conjecture 2.1.** CFH write: "Bearing in mind that G(3) 1 (1,m 2)2 = G(6) 1 (1,m 2) by the Davenport-Hasse relation, this relation is consistent with what is implied by setting k = 6 in the Hecke relations (2.5)." The relation is their prediction `τ⁽⁶⁾(m₁²m₂⁴) = G₃(1, m₂)²G₃(1, m₁)(m₂/m₁)₃²Σ_{m₁=d₁d₂}(d₂/d₁)₃`, from Conjecture 2.1. Section 6 of CFH proves the conjecture over a rational function field for odd `n`, which includes Conjecture 2.1's case `n = 3`.

**Reading.**
- The cubic dual sits on the fourth powers of a GL₂ theta function, a sparse subsequence that a GL₂ summation formula does not reach. For a GL₂ Hecke eigenform the coefficients at fourth powers are governed by the symmetric fourth power, of degree 5. The analogy is consistent with the degree-5 carrier of `ORDER-RANK.md` section 3 (the sextic theta on GL₅).
- A Shimura-type reading of Conjecture 2.1's left side (`θ⁽⁶⁾` convolved with `θ⁽²⁾`) would be a degree-3 object. In `ORDER-RANK.md`'s model it would need `η > 5/13` to go below `7/8` (`orders.eta_to_beat(3, 3, 7/8)`). Isolating the cubic dual inside it needs dividing by a Kubota series. Not pursued.
- Section 4's fixed point applies to a carrier through which the cubic theta component enters as a main term bounded through the Möbius sum. Whether a degree-4 or degree-5 summation formula for `α·conj(G₃)²` isolates it is not settled here.

## 6. Outcome, register entry and signals

**Outcome, scoped.** Through the cubic theta function the cubic route is a fixed point: an input half-plane `θ₀` comes back as `θ₀`, and the generic barrier `σ ≥ 1/2` is the case `θ₀ = 1`. Within section 4's scope, the route improves on a known half-plane only through a treatment of its dual that bounds the cubic theta component, `c·conj(G₃(k))N(k)^{−1/6}·Σ_{(n,k)=1} μ(n)N(n)^{−1/6}`, better than that half-plane allows. Such a treatment proves the smaller half-plane `θ₃(σ)` directly.

The companion's sextic family does not meet this, because absorption removes the Möbius function from its dual's theta component (section 3). *(`PAIRING.md`, section 3: from its cubic theta component. Its sextic theta component keeps the Möbius sum; that component is how the absorbed energy bound becomes the half-plane `θ₆(σ)`.)*

**Register** (CLAUDE.md Check 9(b)). This note amends the sub-entry "Lower-order families with higher-rank theta functions" in STRUCTURAL-REVIEW §6:
- **A barrier bullet:** the fixed point as scoped in section 4, with its gates (O6–O8, C1–C4, T1–T6). Socket: none in the stack. The order-6 template is round 310's `Eis.meanSquare_of_dualMeanSquare`.
- **The Missing Prop stays.** It now carries the remark that, through its theta component, it contains the half-plane `θ₃(σ)`.
- **The attack notes, revised:**
  1. A summation formula for `α·conj(G₃)²` of degree below 4 that does not isolate the cubic theta component.
  2. A saving `η > 3/5` on a degree-4 dual, with the component bounded without input.
  3. The companion's induction at order 3, which would meet the component at each row length of the induction (not checked).

**Signals** (CLAUDE.md Check 9(c)).
- The bias-free numerics of `ORDER-RANK.md` section 5 and of C1 here are circular as evidence for the Missing Prop. At these `Z` the Möbius sum is small because `ζ_K`'s zeros are, numerically, on the line, and the component that matters is proportional to that sum.
- The non-circular content of the numerics:
  - the form of the component, linear in the weight's mass (T1–T5);
  - Heath-Brown's term being that component at the largest mass (C3, C4, T1).

## 7. Reproduce

From this directory:

```
python3 orders.py          # gates O1-O8, exact arithmetic (O6-O8 are this note's)
python3 cubic_gates.py     # gates C1-C4 and T1-T6 on the committed critical_w.json and theta_w.json
```

To regenerate the two JSON files (the prime data to norm `8·10⁴` suffice):

```
gcc -O2 -o periods periods.c -lm
./periods w 80000 > periods_w_8e4.txt
python3 critical.py periods_w_8e4.txt critical_w.json 5000 10000 20000 40000 80000   # about 22 min
python3 theta.py periods_w_8e4.txt theta_w.json 10000 20000 40000 80000             # about 4 min
```

The committed files were written from the norm-`3·10⁵` prime data of section 7 of `ORDER-RANK.md`. The scripts read only primes up to `Z`.
- `critical.py`: the dual mean squares and their exact diagonals, every frequency `k`.
- `theta.py`: the theta component's fit, its projections, and the sextic comparison, squarefree primary frequencies.

**Horizon scan, 2026-10-22.** Searches for Dunn–Radziwiłł's paper, and for large sieves with Möbius or Gauss-sum coefficients, found the paper above and no later result that bounds the cubic theta component for the Möbius weight without an input. Dunn's arXiv:2403.13151 (a bilinear large sieve with kernel the coefficients of a cubic metaplectic cusp form; power savings over primes) was read in its abstract only. Its relation to this component is not examined.

## Check 4 and bearing on RH

**Check 4.**
- Acknowledged:
  - Heath-Brown's cubic large sieve, its failure at the dual block below `ϑ = 1/2`, and Dunn–Radziwiłł's sharpness result, through de Faveri's survey (round 311);
  - Dunn–Radziwiłł's construction of the cubic theta function (rounds 361 onward);
  - Hamdar's cube/residue cancellation in the first moment (register, round 506);
  - the companion's absorbed sextic dual, "ᾱ(n)γ₂(n)Ψ(n)" in its Proposition 5.2 (round 311);
  - Patterson's coefficients of the cubic theta function, and CFH's Hecke relations and Conjecture 2.1 (literature);
  - `ORDER-RANK.md` section 5's reading that the family's `N`-th powers and its dual's theta residues carry the same Möbius sum (this branch).
- New here:
  - the dual mean squares in the regime `H` up to `Z`;
  - the identification of the excess with the cubic theta component, with a single constant, as Dunn–Radziwiłł's correction term (Proposition 9.1, not recorded in the pilot before);
  - the measured Möbius component (projection `0.990 ± 0.049`) and its linearity in the mass;
  - the fixed point `θ₃ = θ₀`, with Heath-Brown's term as its case `θ₀ = 1`. This corrects `ORDER-RANK.md`'s reading that the cubic dual has "no main term in the way";
  - the sextic contrast through absorption;
  - the fourth-power reading of the cubic dual through CFH's Hecke relations.

**Bearing on RH: none.** The note closes, in the scoped sense of section 4, one way through a route to a zero-free half-plane. It gains or verifies no constraint on zeros.
