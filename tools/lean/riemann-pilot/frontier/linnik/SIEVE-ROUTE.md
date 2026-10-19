# The sieve route to Linnik's exponent below 7/3, written out

Round 580. This is SEVEN-THIRDS.md §44's argument, with §45's rule for decomposition, written lemma by lemma. It is meant as a blueprint for a referee and for a Lean formalization.

- The analysis here is at paper level. It is unrefereed, and nothing in it is machine-checked.
- `sieve_route_certificate.py` proves the windows and bounds the loss integral from above (§7). *(Wording scoped in round 581; review F10.)*
- Standard results are stated in the form used and marked as such; their proofs are not repeated, and their sources were not re-read for this file.

## 0. The result

**Theorem.** Assume (H1) and (H2) of §2 with the curve hux. There is `q₀` such that for every `q ≥ q₀` and every `a` prime to `q` there is a prime `p ≡ a (mod q)` with `x ≤ p ≤ 2x`, `x = q^{2.28}`. With the curve cons the same holds with `x = q^{2.25}`.

- (H1) is a theorem of the stack. (H2) with hux is the pair of classical density bounds in Chen–Gupta–Li's statement; cons adds their `7/3`, from a preprint.
- No step uses that `q` is prime.
- With the curve unif of §2 the same holds with `x = q^{2.333}`, below `q^{7/3}` (round 582; SEVEN-THIRDS §47). The curves that depend on `σ` matter only for the lower exponents.
- More generally, the argument gives the theorem at every `L > 2` for which some window strictly inside the Type II window of §3 makes the loss of §6 less than `1`. The certificate proves this at the stated values.

The plan: the Type II estimate (§3) with the separation of variables (§4), then Type I and Harman's fundamental theorem (§5), then the decomposition and the final count (§6).

## 1. Notation

- `q ≥ 3`, `(a, q) = 1`, `L > 2` fixed, and `x = q^L`.
- `ε₁ > 0` is the floor of the sifting (primes below `x^{ε₁}` are handled by the fundamental lemma), and `ε > 0` is the width parameter of the zero windows, with `ε ≤ ε₁²/100`. Statements hold for `q ≥ q₀`. ~~Implied constants depend only on `L`, `ε₁`, `ε` and the fixed smooth bumps.~~ `q₀` and the implied constants depend on `L`, `ε₁`, `ε`, the fixed smooth bumps, the function `η` of (H2) and the decomposition's data (the window and the cells). *(Round 581: the struck list was incomplete; review F10.)*
- `A = {n ∈ [x, 2x] : n ≡ a (mod q)}` and `B = {n ∈ [x, 2x] : (n, q) = 1}`. For a set `C`, `C_d = {n ∈ C : d | n}` and `S(C, z) = #{n ∈ C : p | n ⇒ p ≥ z}`. Then `S(A, (2x)^{1/2})` is the number of primes `p ≡ a (mod q)` in `[x, 2x]`, up to `O(1)`.
- The model of `A` is `B/φ(q)`. For `(d, q) = 1`, `|A_d| = x/(dq) + O(1)` and `|B_d|/φ(q) = x/(dq) + O(2^{ω(q)}/φ(q))`; for `(d, q) > 1` both are `0`.
- For `n` prime to `q`, `1_A(n) − 1_B(n)/φ(q) = (1/φ(q)) Σ_{χ ≠ χ₀} χ̄(a)χ(n)`. Every error term below is a sum of this shape.
- A prime `p` has exponent `α = log p/log x`.
- The window `(u₁, u₂)`, its width `v = u₂ − u₁`, `R = 1 − u₂`, and `U = (u₁, u₂) ∪ (1 − u₂, 1 − u₁)`: §3.
- `ω` is Buchstab's function: `ω(u) = 1/u` on `[1, 2]`, `(uω(u))′ = ω(u − 1)` for `u > 2`, and `0` below `1`.

## 2. Inputs

- **(H1)** For every `q ≥ 1`, every Dirichlet character `χ` mod `q` and every `s` with `Re s > 11/12`, `L(s, χ) ≠ 0`, except at `s = 1` for the trivial character. Lean: `Eis.LFunction_ne_zero_of_re_gt` (`src/DirichletCharHalfPlane.lean`).
- **(H2)** For every `q ≥ 1`, `1/2 ≤ σ ≤ 1` and `T ≥ 2`, `Σ_{χ mod q} N(σ, T, χ) ≤ (qT)^{A(σ)(1−σ)+η(qT)}` with `η(Q) → 0` as `Q → ∞`. Here `N(σ, T, χ)` counts the zeros `ρ = β + iγ` of `L(s, χ)` with `β ≥ σ` and `|γ| ≤ T`, and `A` is one of three curves *(round 584: the count read "two"; review C1)*:
  - hux: `A(σ) = 3/(2 − σ)` for `σ ≤ 3/4` and `3/(3σ − 1)` for `σ ≥ 3/4`;
  - cons: `A(σ) = 3/(2 − σ)` for `σ ≤ 5/7` and `min(7/3, 3/(3σ − 1))` for `σ ≥ 5/7`;
  - unif (round 582): `A(σ) = min(12/5 + 1/2000, 1/(1 − σ))`, Huxley's uniform exponent with a slack of `1/2000`, capped by the trivial count. hux implies it, since `A_hux(σ)(1 − σ) ≤ min(12/5 · (1 − σ), 1)`.

  Chen–Gupta–Li (arXiv:2507.08296v2, p. 2) state the two classical bounds as (1.4) and (1.5); SEVEN-THIRDS §44 quotes them. The `7/3` is their main theorem.
- Used properties of the curves: `A(σ)(1 − σ) ≤ 1` on `[1/2, 1]`. For hux and cons equality holds only at `σ = 1/2`, where `A = 2`; for unif it holds on `[1/2, 1 − 1/(12/5 + 1/2000)]`, and Lemma 2's sum over the dyadic ranges then costs a power of `log x`. The largest value of `A` is `12/5` (hux), `7/3` (cons) or `12/5 + 1/2000` (unif).
- **(T1) Orthogonality.** `Σ_{χ mod q} |Σ_{m≤P} a_mχ(m)|² ≤ (P + q)Σ|a_m|²`. Proof: the left side is `φ(q)Σ_{(r,q)=1}|Σ_{m≡r} a_m|²`, and Cauchy–Schwarz in each class gives at most `φ(q)(P/q + 1)Σ|a_m|²`. Lean: `LinnikHybrid.sum_chars_norm_sq_le` is the first step.
- **(T2) Zeros and `L′/L`** (standard). For `χ ≠ χ₀` mod `q` and `s = σ + iτ` with `1/2 ≤ σ ≤ 2`, `L′/L(s, χ) = Σ_{|γ−τ|≤1} 1/(s − ρ) + O(log(q(|τ| + 2)))`. At most `O(log(q(|τ| + 2)))` zeros have `|γ − τ| ≤ 1`. For an imprimitive `χ` the Euler factors at the primes dividing `q` add `O(log q)` on `σ ≥ 1/2`.
- **(T3) The fundamental lemma** (standard, dimension 1). If `|C_d| = Xg(d) + r_d` for `d | P(z)`, with `g` multiplicative and `0 ≤ g(p) < 1`, then `S(C, z) = X∏_{p<z}(1 − g(p))(1 + O(e^{−s})) + O(Σ_{d≤D, d|P(z)}|r_d|)`, where `s = log D/log z ≥ 1`.
- **(T4) Rough numbers** (standard). For fixed ~~`u ≥ 1`~~ `u > 1` *(round 581: at `u = 1` the count is `O(1)`; review F10)*, `#{n ≤ y : p | n ⇒ p ≥ y^{1/u}} = (ω(u) + o(1))y/log y^{1/u}`. With the prime number theorem this gives the shares in §6 as integrals of `ω`.

## 3. The Type II estimate

Fix the small parameters. For `χ ≠ χ₀` and `y ∈ ℝ` let

`β(χ, y) = max(1/2, max{Re ρ : L(ρ, χ) = 0, |Im ρ − y| ≤ x^ε})`.

By (H1), `β(χ, y) ≤ 11/12`.

**Lemma 1 (smooth prime sums).** Let `φ` be a fixed smooth function supported in `[1/2, 2]`, `x^{ε₁}/2 ≤ Q ≤ 4x` *(round 587: it read `[1, 2]` and `x^{ε₁} ≤ Q ≤ 2x`, but no smooth `φ` supported in `[1, 2]` gives the partition of unity of §4, since at `n = 2^k` only `φ(1) + φ(2) = 0` would contribute; the proof uses only compact support in `(0, ∞)`; review O1)*, `|y| ≤ 2x³` and `χ ≠ χ₀`. Then

`|Σ_p φ(p/Q)χ(p)p^{−iy}| ≪ Q^{β(χ,y)+ε} log² x`.

*Proof.* Put `ψ(u) = φ(u)/log(Qu)`. It is smooth with support in `[1/2, 2]`, with derivatives bounded uniformly in `Q ≥ 4` *(round 587: it read `[1, 2]` and `Q ≥ 2`; review O1)*. So its Mellin transform `ψ̃` is entire and `|ψ̃(σ + iτ)| ≪_{K} (1 + |τ|)^{−K}` for every `K`, uniformly for `σ ∈ [0, 3]`.

- `Σ_n Λ(n)χ(n)n^{−iy}ψ(n/Q)` equals the prime sum plus the prime powers, which contribute `O(Q^{1/2})`. Since `β ≥ 1/2`, that is within the bound.
- By Mellin inversion, `Σ_n Λ(n)χ(n)n^{−iy}ψ(n/Q) = (1/2πi)∫_{(2)} (−L′/L)(s + iy, χ)Q^sψ̃(s) ds`.
- Choose `Y ∈ [x^ε/4, x^ε/2]` so that no zero has `|γ − (y ± Y)| < c/log(qx)`. This is possible because `[y + x^ε/4, y + x^ε/2]` and `[y − x^ε/2, y − x^ε/4]` each hold `O(x^ε log(qx))` ordinates, so the excluded values of `Y` have measure `O(cx^ε)`. *(Round 581: the interval below `y` added; review F10.)* On the horizontal lines `Im s = ±Y`, (T2) gives `|L′/L| ≪ log²(qx)`.
- Move the segment `|Im s| ≤ Y` of the line to `Re s = β + ε`, `β = β(χ, y)`, keeping the rest at `Re s = 2`. The rectangle between holds no zero: a zero there would have `|Im ρ − y| ≤ Y` and `Re ρ > β`. There is no pole, since `χ ≠ χ₀`.
- On the new segment, every zero `ρ` with `|γ − (y + Im s)| ≤ 1` has `|γ − y| ≤ x^ε`, so `Re ρ ≤ β`, `|s + iy − ρ| ≥ ε` and, by (T2), `|L′/L| ≪ ε^{−1}log(qx)`. The segment contributes `≪ Q^{β+ε}ε^{−1}log(qx)`.
- On the horizontal segments, `Q^{Re s} ≤ Q²` and `|ψ̃| ≪ Y^{−K}`. On `Re s = 2`, `|Im s| ≥ Y`, `|L′/L| ≪ 1`. With `K > 3/ε` both are `O(1)`. ∎

**Lemma 2 (characters near zeros).** Let `μ` be a positive measure on `[−2x³, 2x³]` with density at most `D/(1 + |y|)`. For `1/2 < β ≤ 11/12`,

`∫ #{χ ≠ χ₀ : β(χ, y) ≥ β} dμ(y) ≪ D x^{3ε} q^{A(β)(1−β)}`.

For `β = 1/2` the count is at most `φ(q) ≤ q = q^{A(1/2)/2}`, and the integral is at most `qμ(ℝ)`.

*Proof.* For `β > 1/2`, a character counted at `y` has a zero `ρ` with `Re ρ ≥ β` and `|γ − y| ≤ x^ε`. So the integral is at most `Σ_ρ μ([γ − x^ε, γ + x^ε])` over the zeros with `Re ρ ≥ β`, `|γ| ≤ 3x³`. Each term is at most `2x^εD/(1 + max(0, |γ| − x^ε))`. Summing over dyadic ranges `|γ| ∼ V`, (H2) gives `≪ x^{2ε}D Σ_V V^{−1}(qV)^{A(β)(1−β)+η}`. Since `A(β)(1 − β) ≤ 1`, the sum over the `O(log x)` ranges is `≪ x^{3ε}q^{A(β)(1−β)}`. ∎

**The window.** For `β ∈ [1/2, 11/12]` put

- `lower(β) = (A(β)(1 − β)/2 + 1/2 − L(1 − β))/(β − 1/2)` for `β > 1/2`;
- `upper(β) = L − A(β)/2`;

and `u₁ = sup_β lower(β)/L`, `u₂ = min(inf_β upper(β)/L, 1/2)`. They satisfy `u₁ < u₂` and `u₂L > 1` at the certified `L` (§7). Below, `(u₁, u₂)` stands for a window `(u₁′, u₂′)` strictly inside, with `v`, `R` and `U` taken from it; §6 needs nothing more.

**Proposition 3 (Type II).** Let `u ∈ [u₁′, u₂′]`, `P = x^u`, `X = x/P`, with `x` large enough that the range `(P, 2P]` of `W` stays inside the margins of `(u₁′, u₂′)` in `(u₁, u₂)` *(round 581; review F10)*. Let `τ ∈ ℝ^J`, `J ≤ 8/ε₁`, carry the measure `μ` with density `∏ k(τ_i)`, `k(τ) = min(log x, 1/|τ|)` on `|τ| ≤ x²` and `0` outside. Let `h₀(τ), h₁(τ), …, h_K(τ)` be heights of the form `Σ c_iτ_i`, `c_i ∈ {−1, 0, 1}`, `K ≤ 2/ε₁`. Let

- `W(χ, τ) = Σ_{P<m≤2P} a_m(τ)χ(m)m^{−ih₀(τ)}` with `|a_m(τ)| ≤ τ(m)^C`, measurable in `τ`;
- `B(χ, τ) = ∏_{j≤K} Σ_p φ_j(p/Q_j)χ(p)p^{−ih_j(τ)}`, with fixed smooth `φ_j` supported in `[1/2, 2]`, `Q_j ≥ x^{ε₁}/2` and `∏Q_j ≍ X` *(round 587: it read `[1, 2]` and `Q_j ≥ x^{ε₁}`; review O1)*.

Then `∫ Σ_{χ≠χ₀} |W(χ, τ)B(χ, τ)| dμ(τ) ≪ x^{1−δ}` for some `δ > 0` depending on the margins of `(u₁′, u₂′)` inside `(u₁, u₂)`.

*Proof.*

- Cut `[1/2, 11/12]` at `β₀ = 1/2 < β₁ < … < β_N = 11/12` with steps at most `ε`. For each `τ`, put `χ` in bin `i` when `b(χ, τ) = max_j β(χ, h_j(τ))` lies in `[β_i, β_{i+1})`, the last bin being closed at `11/12`, which (H1) allows *(round 581; review F10)*.
- In bin `i`, Lemma 1 gives `|B| ≤ X^{β_i+2ε}(C log² x)^K ≤ X^{β_i+3ε}`.
- Cauchy–Schwarz over `(χ, τ)` in bin `i`, with (T1) at each `τ` (the factor `m^{−ih₀}` joins the coefficients): `∫Σ_χ |W|² dμ ≤ (P + q)P x^ε μ(ℝ^J)`, and `μ(ℝ^J) ≪ (log x)^{2J}`.
- The bin's measure is `∫ #bin_i(τ) dμ ≤ Σ_j ∫ #{χ : β(χ, y) ≥ β_i} dμ_j(y)`, where `μ_j` is the image of `μ` under `h_j`. If `h_j` depends on `τ`, `μ_j` is a convolution of at most `J` kernels `k` and has density `≪ (log x)^{2J}/(1 + |y|)`; if `h_j = 0`, `μ_j` is a point mass at `0`, covered by the proof of Lemma 2, which then counts at one height *(round 581; review F10)*. Lemma 2 gives `≪ x^{4ε}q^{A(β_i)(1−β_i)}`.
- So the bin contributes `≪ x^{6ε}q^{A(β_i)(1−β_i)/2}((P + q)P)^{1/2}X^{β_i}`. With `P = q^m`, `X = q^{L−m}`, this is below `x^{1−δ}` when `m > lower(β_i) + δ′` (if `P ≤ q`) or `m < upper(β_i) − δ′` (if `P ≥ q`), for `δ′` fixed by the margins and `ε` small.
- Bin `0`, `β = 1/2`, has at most `q` characters and the bound `q^{1+L/2}` (if `P ≤ q`) or `q^{(1+m+L)/2}` (if `P ≥ q`). Both are below `x^{1−δ}`, since `L > 2` and `m ≤ u₂L ≤ L − 1`.
- There are `N ≪ 1/ε` bins. ∎

## 4. Separating the variables

By §1, each difference that §5 and §6 need, a count over `A` minus the same count over `B` divided by `φ(q)`, has the form `(1/φ(q)) Σ_{χ≠χ₀} χ̄(a) Σ_{m,r} a_m b_r χ(mr)` over `mr ∈ [x, 2x]` *(round 581: the factor `1/φ(q)` made explicit; review F1)*, where `r` (or `m`) is a product of primes subject to conditions that couple it to the other variable. These conditions are of three kinds:

- comparisons between two primes (`p₂ < p₁`, or the least prime factor of the rough part at least the last sifted prime);
- comparisons of a product of primes with a fixed threshold `z ≤ 2x` (a power of `x`, `(2x)^{1/2}`, or the ends of `[x, 2x]`);
- the dyadic ranges of the single primes, smoothed by a fixed partition of unity `Σ_k φ(n/2^k) = 1` with `φ` smooth and supported in `[1/2, 2]` *(round 587: the support added; review O1)*.

**Lemma 4.** Each such difference equals `(1/φ(q)) ∫ Σ_{χ≠χ₀} χ̄(a)W(χ, τ)B(χ, τ)K(τ) dτ` plus `E` *(round 581: stated for the difference, in the units of counts; review F1)*, with `W`, `B` and the heights as in Proposition 3, `|K(τ)| ≪ ∏ k(τ_i)`, and `E ≪ x^{1−ε₁+2ε}/q + x^{1/2+2ε}`, which is `o(x/(q log x))` since `ε < ε₁/2` and `L > 2`. Coefficients are bounded by `1` or by divisor functions.

*Proof.*

- Truncated Perron at height `T = x²` with `c = 1/log x`: `1[Y < Z] = (1/2πi)∫_{c−iT}^{c+iT}(Z/Y)^s ds/s + O((Z/Y)^c min(1, (T|log(Z/Y)|)^{−1}))`. Multiplying out over the conditions puts each factor at its own height, and the kernels give `K`.
- Two distinct integers up to `2x` differ in ratio by more than `1 + 1/(2x)`. So a comparison between two products of primes errs only when they are equal. The `n` with a repeated prime `p ≥ x^{ε₁}` number `O(x^{1−ε₁}/q + x^{1/2})` in `A`, and `o(x/q)` since `L > 2`.
- Against a fixed threshold `z ≤ 2x`, an error beyond `O(1/x)` needs `|log(z/Y)| < 1/x`. That leaves `O(1)` integers `Y`. Every threshold is at least `x^{ε₁}`, the floor of the sifting, so each such `Y` divides `O(x^{1−ε₁}/q + 1)` elements of `A`. (The floor is a threshold for the primes of Proposition 6's iteration, so `x^{1−v}/q` would be too small here.)
- The factors `(Z/Y)^c` are bounded, and the coefficients and the kernels' masses cost at most `x^{2ε}` in all.
- A coefficient condition such as "the least prime factor `ℓ` of the rough part is at least `p_k`" is separated by writing the rough part with `ℓ` as its own variable. The remaining coefficients stay bounded by `1`. ∎

## 5. Type I and the fundamental theorem

**Lemma 5 (Type I).** For `D ≤ x^{1−1/L−ε}` and `|b_d| ≤ τ(d)^C`, `Σ_{d≤D} |b_d| · ||A_d| − |B_d|/φ(q)| ≪ x^{1−1/L−ε/2}`, which is `o(x/(q log x))`. *Proof:* each difference is `O(1)` (§1). ∎

**Proposition 6 (Harman's fundamental theorem, in the form used).** Let `Ω` be a region of exponents `(α₁, …, α_j)`, `j ≤ 3`, cut out by finitely many conditions of the kinds in §4, with `α₁ + ⋯ + α_j ≤ R`. Let `c_r = ±1` for the products `r = p₁⋯p_j` of primes whose exponents lie in `Ω`, and `c_r = 0` otherwise. Then

`Σ_r c_r S(A_r, x^v) = Σ_r c_r S(B_r, x^v)/φ(q) + O(η(ε₁)Σ_r |c_r| x/(rφ(q) log x)) + O(x^{1−δ}/φ(q))`,

where `η(ε₁) ≪ ε₁^{−2}e^{−κ/ε₁}` with `κ = u₂ − 1/L − ε > 0`, so `η(ε₁) → 0` as `ε₁ → 0`. *(Round 581: corrected. The two error terms read `x/(rq log x)` and `x^{1−δ}/q`, which was false when written: the first holds only when `q` has no small prime factors, and the second was not derived; review F1 and F2.)*

*Proof.* Iterate Buchstab's identity `S(C_m, z) = S(C_m, w) − Σ_{w≤p<z} S(C_{mp}, p)` with `w = x^{ε₁}`, for `C = A` and `C = B/φ(q)` alike, starting from `m = r`, `z = x^v`. Along each branch the partial products `m = rp₁⋯p_k` (`p_k < … < p₁ < x^v`) grow by factors below `x^v`, and the branch stops as soon as `m` lies in `(x^{u₁}, x^{u₂})` or in `(x^{1−u₂}, x^{1−u₁})`.

- If `r ≤ x^{u₁}`, the partial products cannot jump over `(x^{u₁}, x^{u₂})`, whose width in exponent is `v`. Before stopping they stay below `x^{u₂}`.
- If `x^{u₂} ≤ r ≤ x^R`, they enter `(x^{1−u₂}, x^{1−u₁})` in the same way, and before that they stay below `x^{1−u₂}`. If `r ∈ (x^{u₁}, x^{u₂})` the branch stops at once.
- A stopped term `S(C_m, p_k)` is a Type II sum: in the first case `W` is the partial product and `B` is the rest of `n`; in the second case the roles swap. The rest of `n` is a product of at most `1/ε₁` primes, each at least `x^{ε₁}`. Lemma 4 and Proposition 3 bound the difference between `A` and `B/φ(q)` by ~~`x^{1−δ}`~~ `x^{1−δ}/φ(q)` *(round 581: the factor `1/φ(q)` is §1's; review F1)*.
- In the first case `r` is part of `W`, whose coefficients are arbitrary. In the second case `r` is part of `B`: its primes become prime sums, and the conditions that cut out `Ω` are separated by Lemma 4 like the others. Either way one application of Proposition 3 covers the whole sum over `r`. This is why `c_r` is taken to be the indicator of a region (smooth weights in the primes of `r` would also do; round 581, review F5): arbitrary coefficients on `r` would leave `B` without the pointwise bound of Lemma 1. For the same reason the statement is about the sum over `r`, not about each `r` alone.
- The terms `S(C_m, w)` have `m < x^{1−u₂}`. (T3) with `D = x^{1−1/L−ε}/m` and Lemma 5 give the difference `O(e^{−s})` times the main term, plus `O(x^{1−1/L−ε/2})`, with `s = log D/log w ≥ (u₂ − 1/L − ε)/ε₁`, which is positive because `u₂L > 1`.
- Summed over the leaves of the Buchstab tree, the main terms ~~`x/(mq log w)` total at most `x/(rq log w) · exp(Σ_{w≤p<x^v} 1/p) ≪ ε₁^{−2}x/(rq log x)`. With the factor `e^{−s}` this is `η(ε₁)x/(rq log x)`.~~ *(Round 581: retracted, false when written. The product over the primes below `w` leaves out those dividing `q`, since `|A_{md}| = 0` when `(md, q) > 1`, and `∏_{p<w, p|q}(1 − 1/p)^{−1} ≤ q/φ(q)` is unbounded for composite `q`; review F2.)* `(x/(mq))∏_{p<w, p∤q}(1 − 1/p) ≪ x/(mφ(q) log w)` total at most `x/(rφ(q) log w) · exp(Σ_{w≤p<x^v} 1/p) ≪ ε₁^{−2}x/(rφ(q) log x)`. With the factor `e^{−s}` this is `η(ε₁)x/(rφ(q) log x)`.
- There are `O_{ε₁}(1)` levels of iteration, so the errors add up as stated. ∎

## 6. The decomposition and the final count

Buchstab's identity gives

`S(A, (2x)^{1/2}) = S(A, x^v) − Σ_{x^v≤p₁<(2x)^{1/2}} S(A_{p₁}, p₁)`, and for `α₁ ∉ (u₁, u₂)`, `S(A_{p₁}, p₁) = S(A_{p₁}, x^v) − Σ_{x^v≤p₂<p₁} S(A_{p₁p₂}, p₂)`,

and the same for `B/φ(q)`.

- **Evaluable terms.** A term `S(A_m, p)` with `m = p₁⋯p_k` is *evaluable* when some subset sum of `α₁, …, α_k` lies in `U`. Then its `A`-version and its `B`-version divided by `φ(q)` agree up to ~~`x^{1−δ}`~~ `x^{1−δ}/φ(q)` *(round 581; review F1)*: the subset's product is `W` and the rest of `n` is `B` (subset sum in `(u₁, u₂)`), or the reverse (subset sum in `(1 − u₂, 1 − u₁)`). This is Lemma 4 with Proposition 3.
- **Depth 1.** The term `S(A, x^v)` is evaluated by Proposition 6 with `r = 1` (`j = 0`) *(round 581; review F10)*. For `α₁ ∈ (u₁, u₂)` the term is evaluable. Otherwise it is decomposed, and `S(A_{p₁}, x^v)` is evaluated by Proposition 6, since `α₁ ≤ 1/2 + o(1) < R`.
- **Depth 2.** The terms `S(A_{p₁p₂}, p₂)` enter with sign `+`. A term that is not evaluable is either *dropped*, which lowers the count by its `B`-share, or *decomposed* as `S(A_{p₁p₂}, x^v) − Σ_{x^v≤p₃<p₂} S(A_{p₁p₂p₃}, p₃)`, which needs `α₁ + α₂ ≤ R` for Proposition 6.
- **Depth 3.** These terms enter with sign `−`, so each must be evaluable or decomposed again, which needs `α₁ + α₂ + α₃ ≤ R`. Their terms of depth 4 enter with sign `+` and are dropped when not evaluable.
- **The sharp rule.** The complement window is `(R, 1 − u₁)`. A term whose sum `α₁ + ⋯ + α_k` lies in it is evaluable. So a non-evaluable term with that sum below `1 − u₁` has the sum at most `R` and can be decomposed. The certificate decomposes a cell of `(α₁, α₂)` when its largest sums `α₁ + α₂` and `α₁ + α₂ + α₃` (over the `α₃` that may be non-evaluable) stay below `1 − u₁`. The same holds at every point of the cell.
- **Shares.** By (T4) and the prime number theorem, the `B`-count of a dropped family of depth 2 over a region `Ω` is `(1 + o(1))(x/log x)∫_Ω ω((1 − α₁ − α₂)/α₂) dα₁dα₂/(α₁α₂²)`. A family of depth 4 has the integrand `ω((1 − α₁ − ⋯ − α₄)/α₄)/(α₁α₂α₃α₄²)`. The primes dividing `q` change these counts by `o(x/log x)`.
- **The loss** is the sum of the shares of the dropped families, divided by `x/log x`: the integral `loss(L)` that §7 bounds.

**Proposition 7.** `S(A, (2x)^{1/2}) ≥ (1 − loss(L) − O(η(ε₁)) − o(1)) x/(φ(q) log x)`.

*Proof.* Subtract the identity for `B/φ(q)` from that for `A`. The evaluable and evaluated terms cancel up to ~~`x^{1−δ}/q`~~ `x^{1−δ}/φ(q)` *(round 581; review F1)* and `O(η(ε₁))` of the main term (Lemma 4, Propositions 3 and 6). A dropped term has its `A`-version at least `0`, so it costs at most its `B`-share. `S(B, (2x)^{1/2})/φ(q) = (1 + o(1))x/(φ(q) log x)`. ∎

With `loss(L) < 1` and `ε₁` small, the right side is positive for large `q`, which is the theorem.

## 7. The numerics

`sieve_route_certificate.py` proves, with exact tests of the region, of evaluability and of decomposition, and with outward rounding (SEVEN-THIRDS §45):

- windows `(u₁′, u₂′)` inside `(u₁, u₂)`, by exact branch and bound;
- `loss(L) ≤ 0.9757` for unif at `L = 2.333` (round 582) *(round 584: it read `0.9756`, rounded down from the printed `0.9756129805606728`; review F1)*;
- `loss(L) ≤ 0.9521` for hux at `L = 2.28`, and `≤ 0.9117` for cons at `L = 2.25`, with the decomposition of §6 run on those windows, and the bounds `0.7822`, `0.6231` and `0.8293` at hux `2.29`, cons `2.27` and hux `2.32` *(round 584: rounded up. Four of them read `0.9520`, `0.7821`, `0.6230` and `0.8292`, rounded down from the printed `0.95201853…`, `0.78213773…`, `0.62302589…` and `0.82922167…`; review F1)*.

Midpoint estimates put the thresholds of this decomposition between `2.275` and `2.28` (hux) and between `2.24` and `2.245` (cons). They are estimates: they rise as the grid is refined, and the scratch Monte Carlo of round 579's review puts the loss about `0.01` above them near the thresholds (README round 579, O1).

## 8. Status, and what a check needs

**What a referee should check first.**

- Lemma 1 at heights up to `2x³`, with the window `x^ε` and the choice of `Y`. *(Round 587: with §10, at heights up to `2x^ε` only; review F7.)*
- Proposition 3's binning when the factors sit at different heights: the bin is taken by the maximum over the heights, and Lemma 2 is applied to each image measure. *(Round 587: with §10, Proposition 3′ bins by `b(χ)` and uses no Lemma 2; review F7.)*
- Lemma 4's error terms, in particular the thresholds and the separation of the least prime factor. *(Round 587: with §10, Lemmas 4′ and 4″ take Lemma 4's place, and Lemma 4″, the smooth majorants evaluated by Proposition 3′, is the step to check first; review F7.)*
- Proposition 6's stepping argument, the range `m < x^{1−u₂}` of its fundamental-lemma terms, and its coefficients: in the second case `r` sits in the factor bounded through the zeros, so ~~`c_r` must be the indicator of a region~~ `c_r` cannot be arbitrary: the indicator of a region keeps Lemma 1's bound, as do smooth weights in the primes of `r` *(round 581: "must" was too strong; review F5)*.
- §6's signs, and the sharp rule.

**The Lean map** (stack modules that exist, and what is missing).

- In the stack:
  - (H1): `Eis.LFunction_ne_zero_of_re_gt`;
  - orthogonality over characters: `LinnikHybrid.sum_chars_norm_sq_le`, and the hybrid mean value `LinnikHybrid.mean_value_chars`;
  - ~~the density machinery of rounds 524–527:~~ `Linnik.CharDensity` (round 520) *(round 581: the label was wrong; review F6)*, proved by `LinnikTwelve.charDensity_twelve_fifths` with the uniform exponent `12/5 + 54ε`. It counts characters, not zeros, at every height;
  - the deduction `Linnik.linnik_of_charDensity` (round 520), by a contour shift through zero-free rectangles, without the explicit formula over zeros *(round 581: it was called "explicit-formula"; review F6)*.
- Missing:
  - Lemma 1 (contour shifts for smooth prime sums inside zero-free rectangles of height `x^ε`);
  - Lemma 2 (it needs zero counts, or a smoothing that keeps the heights below `x^ε`, where a count of characters suffices; that smoothing is not worked out here, round 581) *(round 586: §10 works it out)*;
  - Proposition 3, the Type II estimate with its bins and the measure `∏ k(τ_i)` *(added in round 581; review F4)*;
  - Lemma 4: Perron's formula truncated at a sharp cut-off, for several conditions at once, each with its own height *(added in round 581; review F4)* *(round 586: §10 replaces it by Lemmas 4′ and 4″)*;
  - Huxley's bound `3(1 − σ)/(3σ − 1)` for each `σ` in `[3/4, 11/12]`. Round 527 proves the uniform `12/5` on that range with one choice of its parameters; Huxley's curve needs a choice that depends on `σ`;
  - Buchstab's identity, the fundamental lemma, Harman's fundamental theorem, and the asymptotics of rough numbers;
  - a kernel-checked bound for the loss. At `L = 2.32` the certificate needs 434 cells of depth 2 and 473 of depth 4, and every bound rests on an enclosure of `ω` on intervals of width `2^{−16}`. Round 579's review counted 518650 of them in a scratch run, up to the argument `8.914`.

**Literature.** IDEAS.md G19 records the literature check of round 580.

## 9. The Lean route (round 582)

**Target.** A theorem with the conclusion of `Linnik.linnik_of_charDensity` (`external/pnt/LinnikDeduction.lean`) and an exponent below `7/3`. For example: for every `q` and every `a` prime to `q` there is a prime `p ≡ a (mod q)` with `p ≤ K q^{2.333}`. The route is §§3–6 with the uniform curve of SEVEN-THIRDS §47, where the loss at `L = 2.333` is certified below `1`.

**Milestones.** Each is a run of rounds. The stack's holdings come from a survey of the pilot, Mathlib and PNT+ at the pinned commit 650d312, made for this round by a subagent (a survey, under Check 3) and spot-checked where stated.

- **M1. Zero counts.** The goal is `Σ_χ N(σ, T, χ) ≤ C(qT)^{(12/5 + 54ε)(1 − σ)}(log qT)^B` for every `T ≥ 2`, counting zeros, since Lemma 2 weights each zero by `1/(1 + |γ|)`. *(Round 586: with §10's smoothing, M1 is not needed for unif: (H2′) follows from the stack's `LinnikTwelve.charDensity_twelve_fifths` with the trivial count. Wording corrected in round 587, review F1.)*
  - The stack counts characters: rounds 524–527 detect one zero per character, and `large_values_chars`, `huxley_large_values` and `fourth_moment` each take one point per character.
  - *(Round 583: `LinnikPoints.large_values_points` (`external/pnt/LinnikPoints.lean`) extends round 521's `large_values_chars` to points `(χ, t)`, any two points of one character at distance at least `1`. A survey made for round 583 by a subagent, and spot-checked by the lead, names four other places where the stack's proofs of the uniform `12/5` take one point per character: the count `|R| ≤ q` (`card_chars_le`); `choose!` in the counting lemmas; the Halász–Montgomery kernel, whose off-diagonal pairs have `χ ≠ χ′` (`LinnikReflect.pair_reflect`, in `LinnikLargeValues.lean`), so that pairs of points of one character bring in the principal character and the pole of `ζ`; and the trivial character, counted as `+1`, which can be left out, since §3 counts only `χ ≠ χ₀`. Its estimates, which are not checked: the range `σ ≤ 3/4` needs re-indexing only, about one round; the Huxley range needs the principal character's kernel, the main risk, roughly 500 to 1000 lines; and a local count of the zeros of `L(s, χ)` by Jensen's formula takes roughly 150 to 300 lines. README round 583. The counting lemmas use the off-line form `large_values_chars_off` (`LinnikHybrid.lean:460`; it read `:479`, the line of its call to `large_values_chars`, corrected in round 587, review F6), which is not yet extended; round 585, review F6.)*
  - Needed: the same estimates over points `(χ, t)`, with several `1`-spaced `t` for each character. Also a local count `#{ρ : |γ − t| ≤ 1} ≪ log q(|t| + 2)` for `L(s, χ)`. The stack has the latter for `ζ` only; for `L(s, χ)` it would follow from Jensen's formula as in PNT+'s `ZerosBound`, with `LFunction_growth`.
  - Why counts of zeros, and not the stack's counts of characters at small heights only: above some height, try the large sieve alone. Take a Perron variable `τ_i` that shifts `W` and a factor `D` of `B = DE`. On `|τ_i| ∼ T`, Cauchy–Schwarz and the hybrid mean value give at most `(X_E/T)((qT + P)P)^{1/2}((qT + X_D)X_D)^{1/2} x^{o(1)}`. When `qT ≥ max(P, X_D)` this is `qx(P X_D)^{−1/2} x^{o(1)}`, which is below `x^{1−δ}` only when `P X_D ≥ q²x^{2δ}`. Among the couplings is the least prime of a rough part against the last sifted prime. There `D` can be as short as `x^{ε₁}`, and `P` can be shorter than `q`, since `u₁L < 1` whenever the window is not empty (`lower(β) < 1` exactly when `upper(β) > 1`). So the large sieve alone does not close this argument at large heights, and it needs the zeros at every height. *(Round 586: that holds with Lemma 4's sharp cut-offs. With §10's smoothing every height is below `x^ε`, and counts of characters suffice.)*
- **M2. Lemma 1.**
  - The stack has `Linnik.norm_Sx_le` (a `Γ` weight at height `0`, with a zero-free rectangle from height `0`) and `SmoothPerron` (compactly supported smoothing).
  - Needed: a height `y` with a zero-free rectangle around it, and weights of compact support. *(Round 586: with §10, heights up to `2x^ε` only, and `Linnik.logDeriv_LFunction_le` in place of (T2).)*
- **M3. Lemma 2 and Proposition 3.**
  - The stack has orthogonality: `LinnikHybrid.sum_chars_norm_sq_le`.
  - Needed: the bins by zeros near heights, and the measure `∏ k(τ_i)`. *(Round 586: with §10, Proposition 3′ bins by `b(χ)` and uses no Lemma 2.)*
- **M4. Lemma 4.** Truncated Perron with a sharp cut-off. The survey found none in the pilot, Mathlib or PNT+. Then the separation of the conditions. *(Round 586: §10 replaces it by Lemmas 4′ and 4″.)*
- **M5. The sieve.** Sifted sets in a progression, Buchstab's identity, and the decomposition to depth 4 as an exact identity. Then Lemma 5, a fundamental lemma of dimension 1, and Proposition 6.
  - Brun's pure sieve does not suffice here. With `w = x^{ε₁}` and level `x^κ`, the sieve parameter `s = κ/ε₁` stays fixed as `x` grows. Truncating inclusion–exclusion at that level leaves an error of about `X(log log w)^s/s!`, which outgrows the main term `≍ X/log w`. So the fundamental lemma proper is needed, from Brun's sieve or the β-sieve.
  - Mathlib has the Selberg upper-bound sieve only.
- **M6. Rough numbers.** `#{n ≤ y : p | n ⇒ p ≥ y^{1/u}} ∼ ω(u) y/log y^{1/u}`, uniformly for `u` in compact subsets of `(1, ∞)` *(round 584: at `u = 1` the count is `O(1)`; review C3)*, with `ω` defined by its delay equation.
  - It follows from the stack's prime number theorem (`psi_isBigO_eleven_twelfths`), by partial summation and induction on the number of prime factors.
  - Mertens' theorem is in PNT+ at 650d312 (`IEANTN/Mertens.lean`, `sum_prime_div_eq`; checked), but not among the vendored files.
- **M7. The loss in Lean.** An enclosure of `ω`, and a bound for the loss integral.
  - ~~With the uniform curve at `L = 2.333` the certificate needs `n = 600`.~~ *(Round 584: retracted, false when written: smaller grids certify too; review F2.)* With the uniform curve at `L = 2.333` the committed certificate runs at `n = 600`, where a scratch count gives 73877 cells of depth 2, 37512 of them decomposed, and about `9.0` million cells of depth 4. ~~The coarser grids tried also certify.~~ *(Round 585: retracted, false when written: `n = 400` was tried and does not certify; review F2.)* Of the coarser grids tried, those from `n = 410` up certify. Round 582's review ran `n = 410` to `450` in steps of 10, and `500` and `550`, all below `1`. At `n = 410` the bound is `0.996775`, with 34634 cells of depth 2 and 2132774 of depth 4, and at `n = 400` it is `1.004279` (scratch, round 584) *(round 587: rounded down from `1.00427943…`; as a bound, `1.004280`; review F5)*. Either grid is too large to replay one by one. A rule of higher order, or exact integration over the polyhedral regions, should shrink it.
  - With hux at `L = 2.32`, 434 cells of depth 2 and 473 of depth 4 suffice, and every bound also rests on the enclosure of `ω`. But hux needs density curves that depend on `σ`, so M1 would have to supply those too. *(Round 586: with §10, as counts of characters.)*
- **M8. Assembly.** Proposition 7, plus the small `q` handled as `linnik_of_charDensity` handles them.

**Order.** ~~M5 and M6 do not depend on the analytic side.~~ *(Round 584: retracted, false when written; review F3.)* M5's combinatorics (sifted sets, Buchstab's identity, the decomposition identity, Lemma 5 and the fundamental lemma) and M6 do not depend on the analytic side. Proposition 6 does, through Proposition 3 and Lemma 4, unless it is stated with the Type II bound as a hypothesis, as Harman's theorem usually is. M1–M4 are the analytic core and carry the most risk, M1 above all, since it reworks rounds 524–527 over points `(χ, t)`. M7 is numerics. The choice between the uniform curve (M1 as stated, a large M7) and hux (M1 with curves in `σ`, a small M7) is open. *(Round 586: with §10 there is no M1 for unif. For hux it becomes hux's curves in `σ` as counts of characters; §8 lists Huxley's as missing. The analytic core is then M2–M4, and the choice turns on M7 against those curves.)*

## 10. Smoothing in place of Perron at height `x²` (round 586)

At paper level and unrefereed, like the rest of this file.

**What it changes.** §8 names a way around Lemma 2's counts of zeros, "a smoothing that keeps the heights below `x^ε`, where a count of characters suffices", and says that it is not worked out. This section works it out.

- Lemma 4′ replaces Lemma 4's sharp cut-offs by smooth ones of width `θ = x^{−ε₂}` in the logarithm. Fourier inversion separates them, and every height is then at most `JT₀ ≤ x^ε`.
- What the smoothing changes is bounded by smooth majorants, which the Type II estimate itself evaluates (Lemma 4″).
- Proposition 3′, the Type II estimate at these heights, needs on the density side only a count of characters, (H2′) *(round 587: "on the density side" added; it also uses (H1), (T1) and Lemma 1; review F4)*.
- With unif, (H2′) follows from a theorem of the stack *(round 587: it read "is a theorem of the stack"; review F1)*. So at paper level the density input of the theorem of §0 with `x = q^{2.333}` is `LinnikTwelve.charDensity_twelve_fifths`, and the Lean route of §9 needs no counts of zeros.

**(H2′)** For every `q ≥ 1`, `1/2 ≤ σ ≤ 1` and `T ≥ 2`, at most `(qT)^{A(σ)(1−σ)+η(qT)}` characters `χ mod q` have a zero of `L(s, χ)` with `Re s ≥ σ` and `|Im s| ≤ T`, where `η(Q) → 0` as `Q → ∞`.

- (H2) implies (H2′), since each character counted has a zero counted in `Σ_χ N(σ, T, χ)`.
- With unif, (H2′) follows from a theorem of the stack and the trivial count *(round 587: it read "is a theorem of the stack"; review F1)*. Put `A_U = 12/5 + 1/2000`.
  - For `σ ≤ 1 − 1/A_U = 2801/4801`, `A(σ)(1 − σ) = 1`, and at most `φ(q) ≤ qT` characters are counted.
  - For `σ > 2801/4801`, `A(σ) = A_U`. `LinnikTwelve.charDensity_twelve_fifths` with `ε = 1/108000` gives `C ≥ 0` with `Linnik.CharDensity A_U 10 C`: at most `C(qT)^{A_U(1−σ)}(log qT)^{10}` characters have such a zero. Take `η(Q) = max(0, log(C(log Q)^{10})/log Q)`.

**The smoothing.** Fix `ε₂` with `0 < ε₂ ≤ min(ε, ε₁)/4`, and put `θ = x^{−ε₂}`, `T₀ = x^{2ε₂}` and `Λ = log(8x)`. Fix smooth functions `g, c : ℝ → [0, 1]` with `g = 0` on `(−∞, 0]`, `g = 1` on `[1, ∞)`, `c = 1` on `[−1, 1]` and `c = 0` outside `[−2, 2]`. Put `G(u) = g(u/θ)c(u/Λ)`.

- `G` is smooth, with values in `[0, 1]` and support in `[0, 2Λ]`.
- For `|u| ≤ Λ`, `1[u > 0] − G(u)` and `1[u ≥ 0] − G(u)` lie in `[0, 1]` and vanish unless `0 ≤ u < θ`.
- `Ĝ(τ) = ∫ G(u)e^{−iuτ} du` satisfies `|Ĝ(τ)| ≤ 2Λ` and `|Ĝ(τ)| ≤ ‖G^{(K)}‖₁|τ|^{−K}` for `K ≥ 1`. By Leibniz's rule, `‖G′‖₁ ≤ ‖g′‖₁ + ‖c′‖₁` and `‖G^{(K)}‖₁ ≪_K θ^{1−K}`. So `|Ĝ(τ)| ≪ k′(τ) = min(Λ, 1/|τ|)`, and `∫_{|τ|>T₀} |Ĝ| ≪_K (θT₀)^{1−K} = x^{−(K−1)ε₂}`.
- By Fourier inversion, `G(log Z − log Y) = (1/2π)∫ Ĝ(τ)Z^{iτ}Y^{−iτ} dτ` for `Y, Z > 0`.

~~Every comparison of Lemma 4 is `1[Y < Z]` or `1[Y ≤ Z]` for numbers `Y, Z ∈ [1, 8x]`, so `|log(Z/Y)| ≤ Λ`.~~ *(Round 587: retracted, false when written: on the supports of the variables `n` can exceed `8x`; review F3.)* Every comparison of Lemma 4 is `1[Y < Z]` or `1[Y ≤ Z]`, and on the term's support `|log(Z/Y)| ≤ Λ` once `x` is large. Primes and thresholds lie in `[x^{ε₁}, 2x]`, a product of the term's primes lies in `[x^{ε₁}, 2^{O(1/ε₁)}x]`, and `n ≥ x^{u₁}`. So every such ratio is at most `2^{O(1/ε₁)}x^{1−ε₁}`.

**Lemma 4′ (smooth separation).** In the setting of Lemma 4, each difference equals `(1/φ(q)) ∫ Σ_{χ≠χ₀} χ̄(a)W(χ, τ)B(χ, τ)K(τ) dτ + E′`, with `τ ∈ [−T₀, T₀]^J`, `W`, `B` and the heights as in Proposition 3, `|K(τ)| ≪ ∏ k′(τ_i)`, and `E′ ≪ x^{1−ε₂/2}/φ(q) + x^{1−δ}/φ(q)`, where `δ` is Proposition 3′'s. That is `o(x/(q log x))`.

*Proof.*

- The least prime factor is separated as in Lemma 4. The term's remaining conditions are a product `∏_{j≤J} 1_j` of comparisons `1_j`, each `1[Y_j < Z_j]` or `1[Y_j ≤ Z_j]`. With `G_j = G(log Z_j − log Y_j)`,

  `∏_j 1_j − ∏_j G_j = Σ_j (∏_{i<j} G_i)(1_j − G_j)(∏_{i>j} 1_i)`,

  and the `j`-th summand is at most `1[N_j]` in absolute value, where `N_j` is the event `Y_j ≤ Z_j < e^θY_j`. Equal products need no separate count.
- In `∏_j G_j`, Fourier inversion gives each prime of `Z_j` the factor `p^{iτ_j}` and each prime of `Y_j` the factor `p^{−iτ_j}`, with the kernel `∏_j Ĝ(τ_j)/2π`. A function of `W` alone, such as its least prime factor, joins `W`'s coefficients. Orthogonality (§1) gives the integral over `τ ∈ ℝ^J`.
- Cutting the integral to `[−T₀, T₀]^J` costs at most `J(C log x)^{J−1}x^{−(K−1)ε₂}` times `max_χ |WB| ≤ x^{1+o(1)}`, since `∫|Ĝ| ≪ log x`. That is `O(1/x)` for `K ≥ 4/ε₂`.
- The terms `1[N_j]`, over `A` and over `B/φ(q)`, are bounded by Lemma 4″. ∎

**Lemma 4″ (near-boundary terms).** For a term and one of its comparisons `j`, let `M_j(n)` count the representations of `n` in the term's variables for which `N_j` holds, weighted by the absolute values of their coefficients and by the primes' dyadic weights. Then `Σ_{n∈A} M_j(n)` and `Σ_{n∈B} M_j(n)/φ(q)` are both `≪ x^{1−ε₂/2}/φ(q) + x^{1−δ}/φ(q)`.

*Proof.*

- **A smooth majorant.** Conditions on `W` alone are part of its coefficients and are kept. Every other condition except `N_j` and `n ∈ [x, 2x]` is dropped, since each indicator is at most `1`.
  - `1[N_j]` is replaced by `H(log(Z_j/Y_j)/θ)`, where `H ≥ 0` is a fixed smooth function, at least `1` on `[0, 1]` and `0` outside `[−1, 2]`.
  - `1[x ≤ n ≤ 2x]` is replaced by `F(log n)`, where `F` is smooth, `1` on `[log x, log 2x]`, `0` outside `[log x − θ, log 2x + θ]`, with values in `[0, 1]` and the derivative bounds of `G`.
  - The result `M̃_j` is at least `M_j` on `[x, 2x]`, the only place where `M_j` is used *(round 587: the range added; review F3)*. It has the shape of the term, with `W`'s range and the primes' smooth dyadic weights unchanged and with no sharp condition that couples variables.
- **The model.** Let `B̃` be the set of `n ∈ [xe^{−θ}, 2xe^θ]` prime to `q`. Each `n` has at most `τ(n)^{O(1)} = x^{o(1)}` representations.
  - If `N_j` compares two primes `p ≤ p′`, both at least `x^{ε₁}` (one of them may be the least prime factor of `W`), then `p′` lies within `3θp` of `p`. Such `n` number `≪ Σ_{p≥x^{ε₁}} (θp + 1)x/p² ≪ x(θ log log x + x^{−ε₁})`.
  - If `N_j` compares a product `Y` of primes with a threshold `z ≥ x^{ε₁}`, then `Y` lies within `3θz` of `z`. Such `n` number `≪ (θz + 1)x/z ≪ x(θ + x^{−ε₁})`.
  - So `Σ_{n∈B̃} M̃_j(n) ≪ x^{1−min(ε₁, ε₂)+o(1)} ≤ x^{1−ε₂/2}`, which bounds `Σ_{n∈B} M_j(n)`.
- **The count over `A`.** Let `Ã` be the set of `n ∈ [xe^{−θ}, 2xe^θ]` with `n ≡ a (mod q)`. Then `Σ_{n∈Ã} M̃_j(n) = Σ_{n∈B̃} M̃_j(n)/φ(q) + (1/φ(q)) Σ_{χ≠χ₀} χ̄(a) Σ_n M̃_j(n)χ(n)`. `M̃_j` has smooth conditions only. So Fourier inversion separates them as in Lemma 4′, with no near-boundary terms, and Proposition 3′ bounds the character sum by `x^{1−δ}`. The coefficients of `W` are `|a_W|` times the twists, at most `τ(W)^C`. ∎

**Proposition 3′.** Proposition 3 holds with `μ` replaced by the measure with density `∏ k′(τ_i)` on `[−T₀, T₀]^J`, and with (H2′) in place of (H2). Lemma 1 is used only at heights `|y| ≤ JT₀`, and Lemma 2 is not used.

*Proof.* As for Proposition 3, with the bins taken by `b(χ) = max(1/2, max{Re ρ : L(ρ, χ) = 0, |Im ρ| ≤ JT₀ + x^ε})`, which does not depend on `τ`.

- Every height on the support has `|h_j(τ)| ≤ JT₀`, so `β(χ, h_j(τ)) ≤ b(χ)`. In bin `i`, Lemma 1 gives `|B| ≤ X^{β_i+3ε}` as before.
- (H2′) at `T = JT₀ + x^ε ≤ 2x^ε` counts at most `(2qx^ε)^{A(β_i)(1−β_i)+η} ≪ x^{2ε}q^{A(β_i)(1−β_i)}` characters with `b(χ) ≥ β_i`, since `A(β)(1 − β) ≤ 1`. This replaces Lemma 2's bound `x^{4ε}q^{A(β_i)(1−β_i)}`.
- `μ(ℝ^J) ≪ (2 + 2 log(ΛT₀))^J ≪ (log x)^J`. The rest of the proof of Proposition 3 is unchanged. ∎

**Consequence.**

- Proposition 6, §6 and Proposition 7 use Lemma 4 and Proposition 3 only through the bound `x^{1−δ}/φ(q)` for each difference. Lemma 4′ with Proposition 3′ gives `x^{1−δ}/φ(q) + x^{1−ε₂/2}/φ(q)`.
- So the theorem of §0 holds with (H2′) in place of (H2), for each curve, at the exponents certified in §7.
- With unif, (H1) is a theorem of the stack, `Eis.LFunction_ne_zero_of_re_gt`, and (H2′) follows from one, `LinnikTwelve.charDensity_twelve_fifths`, with the trivial count *(round 587: it read "(H1) and (H2′) are theorems of the stack"; review F1)*. So at paper level, with (H1) and (H2′) from the stack and the standard inputs (T1)–(T4) of §2, the theorem holds with `x = q^{2.333}`, below `q^{7/3}`.

**For Lean** (this revises §9).

- ~~M1 is not needed: (H2′) is `Linnik.CharDensity`.~~ *(Round 587: retracted, false when written: unscoped, and (H2′) is not itself a `Linnik.CharDensity`; review F1.)* M1 is not needed for unif: (H2′) follows from `LinnikTwelve.charDensity_twelve_fifths` with the trivial count. For hux, M1 becomes hux's curves in `σ` as counts of characters (§9, Order).
- M2 is Lemma 1 at heights `|y| ≤ 2x^ε` only. ~~The contour of its proof stays in the rectangle `|Im s − y| ≤ x^ε`, `Re s > β(χ, y)`, which holds no zero by the definition of `β(χ, y)`. So `L′/L` can be bounded on it by `Linnik.logDeriv_LFunction_le` (`LinnikChar.lean`), in place of (T2): for `σ ≥ θ′ > θ ≥ 1/2` it bounds~~ *(Round 587: retracted, false when written: the contour's tails on `Re s = 2` leave the rectangle, and the hypothesis `θ′ < 3/2` was left out; review F2.)* The part of its contour off the line `Re s = 2` stays in the rectangle `|Im s − y| ≤ x^ε`, `Re s > β(χ, y)`, which holds no zero by the definition of `β(χ, y)`. There `L′/L` can be bounded by `Linnik.logDeriv_LFunction_le` (`LinnikChar.lean`), in place of (T2); on the tails at `Re s = 2`, `ChiUniform.logDeriv_LFunction_right` gives `‖L′/L‖ ≤ −ζ′/ζ(3/2)`. For `1/2 ≤ θ < θ′ < 3/2` and `σ ≥ θ′`, `logDeriv_LFunction_le` bounds `‖L′/L(σ + it, χ)‖` by `KL θ θ′(log(q + 2) + log(|t| + 4))` when `L(·, χ)` has no zero in the open disc of radius `3/2 − θ` about `3/2 + it`. With `θ = β(χ, y) + ε/2` and `θ′ = β(χ, y) + ε`, that disc lies in the rectangle when `|t − y| ≤ x^ε − 1`.
- M3 is Proposition 3′: bins by `b(χ)`, (T1) and Cauchy–Schwarz, with no Lemma 2.
- M4 is Lemmas 4′ and 4″ in place of the sharp truncated Perron formula: Fourier inversion of a smooth function of compact support (Mathlib), its decay from its derivatives, and the majorants.
- M5–M8 are unchanged.
