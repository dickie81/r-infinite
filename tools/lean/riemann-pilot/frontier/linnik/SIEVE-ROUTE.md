# The sieve route to Linnik's exponent below 7/3, written out

Round 580. This is SEVEN-THIRDS.md §44's argument, with §45's rule for decomposition, written lemma by lemma. It is meant as a blueprint for a referee and for a Lean formalization.

- The analysis here is at paper level. It is unrefereed, and nothing in it is machine-checked.
- The numerics (the windows and the loss) are certified by `sieve_route_certificate.py` (§7).
- Standard results are stated in the form used and marked as such; their proofs are not repeated, and their sources were not re-read for this file.

## 0. The result

**Theorem.** Assume (H1) and (H2) of §2 with the curve hux. There is `q₀` such that for every `q ≥ q₀` and every `a` prime to `q` there is a prime `p ≡ a (mod q)` with `x ≤ p ≤ 2x`, `x = q^{2.28}`. With the curve cons the same holds with `x = q^{2.25}`.

- (H1) is a theorem of the stack. (H2) with hux is the pair of classical density bounds in Chen–Gupta–Li's statement; cons adds their `7/3`, from a preprint.
- No step uses that `q` is prime.
- More generally, the argument gives the theorem at every `L > 2` for which some window strictly inside the Type II window of §3 makes the loss of §6 less than `1`. The certificate proves this at the stated values.

The plan: the Type II estimate (§3) with the separation of variables (§4), then Type I and Harman's fundamental theorem (§5), then the decomposition and the final count (§6).

## 1. Notation

- `q ≥ 3`, `(a, q) = 1`, `L > 2` fixed, and `x = q^L`.
- `ε₁ > 0` is the floor of the sifting (primes below `x^{ε₁}` are handled by the fundamental lemma), and `ε > 0` is the width parameter of the zero windows, with `ε ≤ ε₁²/100`. Statements hold for `q ≥ q₀(L, ε₁, ε)`. Implied constants depend only on `L`, `ε₁`, `ε` and the fixed smooth bumps.
- `A = {n ∈ [x, 2x] : n ≡ a (mod q)}` and `B = {n ∈ [x, 2x] : (n, q) = 1}`. For a set `C`, `C_d = {n ∈ C : d | n}` and `S(C, z) = #{n ∈ C : p | n ⇒ p ≥ z}`. Then `S(A, (2x)^{1/2})` is the number of primes `p ≡ a (mod q)` in `[x, 2x]`, up to `O(1)`.
- The model of `A` is `B/φ(q)`. For `(d, q) = 1`, `|A_d| = x/(dq) + O(1)` and `|B_d|/φ(q) = x/(dq) + O(2^{ω(q)}/φ(q))`; for `(d, q) > 1` both are `0`.
- For `n` prime to `q`, `1_A(n) − 1_B(n)/φ(q) = (1/φ(q)) Σ_{χ ≠ χ₀} χ̄(a)χ(n)`. Every error term below is a sum of this shape.
- A prime `p` has exponent `α = log p/log x`.
- The window `(u₁, u₂)`, its width `v = u₂ − u₁`, `R = 1 − u₂`, and `U = (u₁, u₂) ∪ (1 − u₂, 1 − u₁)`: §3.
- `ω` is Buchstab's function: `ω(u) = 1/u` on `[1, 2]`, `(uω(u))′ = ω(u − 1)` for `u > 2`, and `0` below `1`.

## 2. Inputs

- **(H1)** For every `q ≥ 1`, every Dirichlet character `χ` mod `q` and every `s` with `Re s > 11/12`, `L(s, χ) ≠ 0`, except at `s = 1` for the trivial character. Lean: `Eis.LFunction_ne_zero_of_re_gt` (`src/DirichletCharHalfPlane.lean`).
- **(H2)** For every `q ≥ 1`, `1/2 ≤ σ ≤ 1` and `T ≥ 2`, `Σ_{χ mod q} N(σ, T, χ) ≤ (qT)^{A(σ)(1−σ)+η(qT)}` with `η(Q) → 0` as `Q → ∞`. Here `N(σ, T, χ)` counts the zeros `ρ = β + iγ` of `L(s, χ)` with `β ≥ σ` and `|γ| ≤ T`, and `A` is one of two curves:
  - hux: `A(σ) = 3/(2 − σ)` for `σ ≤ 3/4` and `3/(3σ − 1)` for `σ ≥ 3/4`;
  - cons: `A(σ) = 3/(2 − σ)` for `σ ≤ 5/7` and `min(7/3, 3/(3σ − 1))` for `σ ≥ 5/7`.

  Chen–Gupta–Li (arXiv:2507.08296v2, p. 2) state the two classical bounds as (1.4) and (1.5); SEVEN-THIRDS §44 quotes them. The `7/3` is their main theorem.
- Used properties of the curves: `A(σ)(1 − σ) ≤ 1` on `[1/2, 1]`, with equality only at `σ = 1/2`, where `A = 2`; the largest value of `A` is `12/5` (hux) or `7/3` (cons).
- **(T1) Orthogonality.** `Σ_{χ mod q} |Σ_{m≤P} a_mχ(m)|² ≤ (P + q)Σ|a_m|²`. Proof: the left side is `φ(q)Σ_{(r,q)=1}|Σ_{m≡r} a_m|²`, and Cauchy–Schwarz in each class gives at most `φ(q)(P/q + 1)Σ|a_m|²`. Lean: `LinnikHybrid.sum_chars_norm_sq_le` is the first step.
- **(T2) Zeros and `L′/L`** (standard). For `χ ≠ χ₀` mod `q` and `s = σ + iτ` with `1/2 ≤ σ ≤ 2`, `L′/L(s, χ) = Σ_{|γ−τ|≤1} 1/(s − ρ) + O(log(q(|τ| + 2)))`. At most `O(log(q(|τ| + 2)))` zeros have `|γ − τ| ≤ 1`. For an imprimitive `χ` the Euler factors at the primes dividing `q` add `O(log q)` on `σ ≥ 1/2`.
- **(T3) The fundamental lemma** (standard, dimension 1). If `|C_d| = Xg(d) + r_d` for `d | P(z)`, with `g` multiplicative and `0 ≤ g(p) < 1`, then `S(C, z) = X∏_{p<z}(1 − g(p))(1 + O(e^{−s})) + O(Σ_{d≤D, d|P(z)}|r_d|)`, where `s = log D/log z ≥ 1`.
- **(T4) Rough numbers** (standard). For fixed `u ≥ 1`, `#{n ≤ y : p | n ⇒ p ≥ y^{1/u}} = (ω(u) + o(1))y/log y^{1/u}`. With the prime number theorem this gives the shares in §6 as integrals of `ω`.

## 3. The Type II estimate

Fix the small parameters. For `χ ≠ χ₀` and `y ∈ ℝ` let

`β(χ, y) = max(1/2, max{Re ρ : L(ρ, χ) = 0, |Im ρ − y| ≤ x^ε})`.

By (H1), `β(χ, y) ≤ 11/12`.

**Lemma 1 (smooth prime sums).** Let `φ` be a fixed smooth function supported in `[1, 2]`, `x^{ε₁} ≤ Q ≤ 2x`, `|y| ≤ 2x³` and `χ ≠ χ₀`. Then

`|Σ_p φ(p/Q)χ(p)p^{−iy}| ≪ Q^{β(χ,y)+ε} log² x`.

*Proof.* Put `ψ(u) = φ(u)/log(Qu)`. It is smooth with support in `[1, 2]`, with derivatives bounded uniformly in `Q ≥ 2`. So its Mellin transform `ψ̃` is entire and `|ψ̃(σ + iτ)| ≪_{K} (1 + |τ|)^{−K}` for every `K`, uniformly for `σ ∈ [0, 3]`.

- `Σ_n Λ(n)χ(n)n^{−iy}ψ(n/Q)` equals the prime sum plus the prime powers, which contribute `O(Q^{1/2})`. Since `β ≥ 1/2`, that is within the bound.
- By Mellin inversion, `Σ_n Λ(n)χ(n)n^{−iy}ψ(n/Q) = (1/2πi)∫_{(2)} (−L′/L)(s + iy, χ)Q^sψ̃(s) ds`.
- Choose `Y ∈ [x^ε/4, x^ε/2]` so that no zero has `|γ − (y ± Y)| < c/log(qx)`. This is possible because `[y + x^ε/4, y + x^ε/2]` holds `O(x^ε log(qx))` ordinates. On the horizontal lines `Im s = ±Y`, (T2) gives `|L′/L| ≪ log²(qx)`.
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

**Proposition 3 (Type II).** Let `u ∈ [u₁′, u₂′]`, `P = x^u`, `X = x/P`. Let `τ ∈ ℝ^J`, `J ≤ 8/ε₁`, carry the measure `μ` with density `∏ k(τ_i)`, `k(τ) = min(log x, 1/|τ|)` on `|τ| ≤ x²` and `0` outside. Let `h₀(τ), h₁(τ), …, h_K(τ)` be heights of the form `Σ c_iτ_i`, `c_i ∈ {−1, 0, 1}`, `K ≤ 2/ε₁`. Let

- `W(χ, τ) = Σ_{P<m≤2P} a_m(τ)χ(m)m^{−ih₀(τ)}` with `|a_m(τ)| ≤ τ(m)^C`, measurable in `τ`;
- `B(χ, τ) = ∏_{j≤K} Σ_p φ_j(p/Q_j)χ(p)p^{−ih_j(τ)}`, with fixed smooth `φ_j` supported in `[1, 2]`, `Q_j ≥ x^{ε₁}` and `∏Q_j ≍ X`.

Then `∫ Σ_{χ≠χ₀} |W(χ, τ)B(χ, τ)| dμ(τ) ≪ x^{1−δ}` for some `δ > 0` depending on the margins of `(u₁′, u₂′)` inside `(u₁, u₂)`.

*Proof.*

- Cut `[1/2, 11/12]` at `β₀ = 1/2 < β₁ < … < β_N = 11/12` with steps at most `ε`. For each `τ`, put `χ` in bin `i` when `b(χ, τ) = max_j β(χ, h_j(τ))` lies in `[β_i, β_{i+1})`.
- In bin `i`, Lemma 1 gives `|B| ≤ X^{β_i+2ε}(C log² x)^K ≤ X^{β_i+3ε}`.
- Cauchy–Schwarz over `(χ, τ)` in bin `i`, with (T1) at each `τ` (the factor `m^{−ih₀}` joins the coefficients): `∫Σ_χ |W|² dμ ≤ (P + q)P x^ε μ(ℝ^J)`, and `μ(ℝ^J) ≪ (log x)^{2J}`.
- The bin's measure is `∫ #bin_i(τ) dμ ≤ Σ_j ∫ #{χ : β(χ, y) ≥ β_i} dμ_j(y)`, where `μ_j` is the image of `μ` under `h_j`. If `h_j` depends on `τ`, `μ_j` is a convolution of at most `J` kernels `k` and has density `≪ (log x)^{2J}/(1 + |y|)`; if `h_j = 0`, `μ_j` is a point mass at `0`, covered by Lemma 2 in the same way. Lemma 2 gives `≪ x^{4ε}q^{A(β_i)(1−β_i)}`.
- So the bin contributes `≪ x^{6ε}q^{A(β_i)(1−β_i)/2}((P + q)P)^{1/2}X^{β_i}`. With `P = q^m`, `X = q^{L−m}`, this is below `x^{1−δ}` when `m > lower(β_i) + δ′` (if `P ≤ q`) or `m < upper(β_i) − δ′` (if `P ≥ q`), for `δ′` fixed by the margins and `ε` small.
- Bin `0`, `β = 1/2`, has at most `q` characters and the bound `q^{1+L/2}` (if `P ≤ q`) or `q^{(1+m+L)/2}` (if `P ≥ q`). Both are below `x^{1−δ}`, since `L > 2` and `m ≤ u₂L ≤ L − 1`.
- There are `N ≪ 1/ε` bins. ∎

## 4. Separating the variables

The sums of §5 and §6 have the form `Σ_{χ≠χ₀} χ̄(a) Σ_{m,r} a_m b_r χ(mr)` over `mr ∈ [x, 2x]`, where `r` (or `m`) is a product of primes subject to conditions that couple it to the other variable. These conditions are of three kinds:

- comparisons between two primes (`p₂ < p₁`, or the least prime factor of the rough part at least the last sifted prime);
- comparisons of a product of primes with a fixed threshold `z ≤ 2x` (a power of `x`, `(2x)^{1/2}`, or the ends of `[x, 2x]`);
- the dyadic ranges of the single primes, smoothed by a fixed partition of unity `Σ_k φ(n/2^k) = 1`.

**Lemma 4.** Each such sum, and its version for `B/φ(q)`, equals an integral `∫ Σ_χ χ̄(a)W(χ, τ)B(χ, τ)K(τ) dτ` plus `E`, with `W`, `B` and the heights as in Proposition 3, `|K(τ)| ≪ ∏ k(τ_i)`, and `E ≪ x^{1−ε₁+2ε}/q + x^{1/2+2ε}`, which is `o(x/(q log x))` since `ε < ε₁/2` and `L > 2`. Coefficients are bounded by `1` or by divisor functions.

*Proof.*

- Truncated Perron at height `T = x²` with `c = 1/log x`: `1[Y < Z] = (1/2πi)∫_{c−iT}^{c+iT}(Z/Y)^s ds/s + O((Z/Y)^c min(1, (T|log(Z/Y)|)^{−1}))`. Multiplying out over the conditions puts each factor at its own height, and the kernels give `K`.
- Two distinct integers up to `2x` differ in ratio by more than `1 + 1/(2x)`. So a comparison between two products of primes errs only when they are equal. The `n` with a repeated prime `p ≥ x^{ε₁}` number `O(x^{1−ε₁}/q + x^{1/2})` in `A`, and `o(x/q)` since `L > 2`.
- Against a fixed threshold `z ≤ 2x`, an error beyond `O(1/x)` needs `|log(z/Y)| < 1/x`. That leaves `O(1)` integers `Y`. Every threshold is at least `x^{ε₁}`, the floor of the sifting, so each such `Y` divides `O(x^{1−ε₁}/q + 1)` elements of `A`. (The floor is a threshold for the primes of Proposition 6's iteration, so `x^{1−v}/q` would be too small here.)
- The factors `(Z/Y)^c` are bounded, and the coefficients and the kernels' masses cost at most `x^{2ε}` in all.
- A coefficient condition such as "the least prime factor `ℓ` of the rough part is at least `p_k`" is separated by writing the rough part with `ℓ` as its own variable. The remaining coefficients stay bounded by `1`. ∎

## 5. Type I and the fundamental theorem

**Lemma 5 (Type I).** For `D ≤ x^{1−1/L−ε}` and `|b_d| ≤ τ(d)^C`, `Σ_{d≤D} |b_d| · ||A_d| − |B_d|/φ(q)| ≪ x^{1−1/L−ε/2}`, which is `o(x/(q log x))`. *Proof:* each difference is `O(1)` (§1). ∎

**Proposition 6 (Harman's fundamental theorem, in the form used).** Let `Ω` be a region of exponents `(α₁, …, α_j)`, `j ≤ 3`, cut out by finitely many conditions of the kinds in §4, with `α₁ + ⋯ + α_j ≤ R`. Let `c_r = ±1` for the products `r = p₁⋯p_j` of primes whose exponents lie in `Ω`, and `c_r = 0` otherwise. Then

`Σ_r c_r S(A_r, x^v) = Σ_r c_r S(B_r, x^v)/φ(q) + O(η(ε₁)Σ_r |c_r| x/(rq log x)) + O(x^{1−δ}/q)`,

where `η(ε₁) ≪ ε₁^{−2}e^{−κ/ε₁}` with `κ = u₂ − 1/L − ε > 0`, so `η(ε₁) → 0` as `ε₁ → 0`.

*Proof.* Iterate Buchstab's identity `S(C_m, z) = S(C_m, w) − Σ_{w≤p<z} S(C_{mp}, p)` with `w = x^{ε₁}`, for `C = A` and `C = B/φ(q)` alike, starting from `m = r`, `z = x^v`. Along each branch the partial products `m = rp₁⋯p_k` (`p_k < … < p₁ < x^v`) grow by factors below `x^v`, and the branch stops as soon as `m` lies in `(x^{u₁}, x^{u₂})` or in `(x^{1−u₂}, x^{1−u₁})`.

- If `r ≤ x^{u₁}`, the partial products cannot jump over `(x^{u₁}, x^{u₂})`, whose width in exponent is `v`. Before stopping they stay below `x^{u₂}`.
- If `x^{u₂} ≤ r ≤ x^R`, they enter `(x^{1−u₂}, x^{1−u₁})` in the same way, and before that they stay below `x^{1−u₂}`. If `r ∈ (x^{u₁}, x^{u₂})` the branch stops at once.
- A stopped term `S(C_m, p_k)` is a Type II sum: in the first case `W` is the partial product and `B` is the rest of `n`; in the second case the roles swap. The rest of `n` is a product of at most `1/ε₁` primes, each at least `x^{ε₁}`. Lemma 4 and Proposition 3 bound the difference between `A` and `B/φ(q)` by `x^{1−δ}`.
- In the first case `r` is part of `W`, whose coefficients are arbitrary. In the second case `r` is part of `B`: its primes become prime sums, and the conditions that cut out `Ω` are separated by Lemma 4 like the others. Either way one application of Proposition 3 covers the whole sum over `r`. This is why `c_r` is the indicator of a region: arbitrary coefficients on `r` would leave `B` without the pointwise bound of Lemma 1. For the same reason the statement is about the sum over `r`, not about each `r` alone.
- The terms `S(C_m, w)` have `m < x^{1−u₂}`. (T3) with `D = x^{1−1/L−ε}/m` and Lemma 5 give the difference `O(e^{−s})` times the main term, plus `O(x^{1−1/L−ε/2})`, with `s = log D/log w ≥ (u₂ − 1/L − ε)/ε₁`, which is positive because `u₂L > 1`.
- Summed over the leaves of the Buchstab tree, the main terms `x/(mq log w)` total at most `x/(rq log w) · exp(Σ_{w≤p<x^v} 1/p) ≪ ε₁^{−2}x/(rq log x)`. With the factor `e^{−s}` this is `η(ε₁)x/(rq log x)`.
- There are `O_{ε₁}(1)` levels of iteration, so the errors add up as stated. ∎

## 6. The decomposition and the final count

Buchstab's identity gives

`S(A, (2x)^{1/2}) = S(A, x^v) − Σ_{x^v≤p₁<(2x)^{1/2}} S(A_{p₁}, p₁)`, and for `α₁ ∉ (u₁, u₂)`, `S(A_{p₁}, p₁) = S(A_{p₁}, x^v) − Σ_{x^v≤p₂<p₁} S(A_{p₁p₂}, p₂)`,

and the same for `B/φ(q)`.

- **Evaluable terms.** A term `S(A_m, p)` with `m = p₁⋯p_k` is *evaluable* when some subset sum of `α₁, …, α_k` lies in `U`. Then its `A`- and `B`-versions agree up to `x^{1−δ}`: the subset's product is `W` and the rest of `n` is `B` (subset sum in `(u₁, u₂)`), or the reverse (subset sum in `(1 − u₂, 1 − u₁)`). This is Lemma 4 with Proposition 3.
- **Depth 1.** For `α₁ ∈ (u₁, u₂)` the term is evaluable. Otherwise it is decomposed, and `S(A_{p₁}, x^v)` is evaluated by Proposition 6, since `α₁ ≤ 1/2 + o(1) < R`.
- **Depth 2.** The terms `S(A_{p₁p₂}, p₂)` enter with sign `+`. A term that is not evaluable is either *dropped*, which lowers the count by its `B`-share, or *decomposed* as `S(A_{p₁p₂}, x^v) − Σ_{x^v≤p₃<p₂} S(A_{p₁p₂p₃}, p₃)`, which needs `α₁ + α₂ ≤ R` for Proposition 6.
- **Depth 3.** These terms enter with sign `−`, so each must be evaluable or decomposed again, which needs `α₁ + α₂ + α₃ ≤ R`. Their terms of depth 4 enter with sign `+` and are dropped when not evaluable.
- **The sharp rule.** The complement window is `(R, 1 − u₁)`. A term whose sum `α₁ + ⋯ + α_k` lies in it is evaluable. So a non-evaluable term with that sum below `1 − u₁` has the sum at most `R` and can be decomposed. The certificate decomposes a cell of `(α₁, α₂)` when its largest sums `α₁ + α₂` and `α₁ + α₂ + α₃` (over the `α₃` that may be non-evaluable) stay below `1 − u₁`. The same holds at every point of the cell.
- **Shares.** By (T4) and the prime number theorem, the `B`-count of a dropped family of depth 2 over a region `Ω` is `(1 + o(1))(x/log x)∫_Ω ω((1 − α₁ − α₂)/α₂) dα₁dα₂/(α₁α₂²)`. A family of depth 4 has the integrand `ω((1 − α₁ − ⋯ − α₄)/α₄)/(α₁α₂α₃α₄²)`. The primes dividing `q` change these counts by `o(x/log x)`.
- **The loss** is the sum of the shares of the dropped families, divided by `x/log x`: the integral `loss(L)` that §7 bounds.

**Proposition 7.** `S(A, (2x)^{1/2}) ≥ (1 − loss(L) − O(η(ε₁)) − o(1)) x/(φ(q) log x)`.

*Proof.* Subtract the identity for `B/φ(q)` from that for `A`. The evaluable and evaluated terms cancel up to `x^{1−δ}/q` and `O(η(ε₁))` of the main term (Lemma 4, Propositions 3 and 6). A dropped term has its `A`-version at least `0`, so it costs at most its `B`-share. `S(B, (2x)^{1/2})/φ(q) = (1 + o(1))x/(φ(q) log x)`. ∎

With `loss(L) < 1` and `ε₁` small, the right side is positive for large `q`, which is the theorem.

## 7. The numerics

`sieve_route_certificate.py` proves, with exact tests of the region, of evaluability and of decomposition, and with outward rounding (SEVEN-THIRDS §45):

- windows `(u₁′, u₂′)` inside `(u₁, u₂)`, by exact branch and bound;
- `loss(L) ≤ 0.9520` for hux at `L = 2.28`, and `≤ 0.9117` for cons at `L = 2.25`, with the decomposition of §6 run on those windows, and the bounds `0.7821`, `0.6230` and `0.8292` at hux `2.29`, cons `2.27` and hux `2.32`.

Midpoint estimates put the thresholds of this decomposition between `2.275` and `2.28` (hux) and between `2.24` and `2.245` (cons). They are estimates: they rise as the grid is refined, and the scratch Monte Carlo of round 579's review puts the loss about `0.01` above them near the thresholds (README round 579, O1).

## 8. Status, and what a check needs

**What a referee should check first.**

- Lemma 1 at heights up to `2x³`, with the window `x^ε` and the choice of `Y`.
- Proposition 3's binning when the factors sit at different heights: the bin is taken by the maximum over the heights, and Lemma 2 is applied to each image measure.
- Lemma 4's error terms, in particular the thresholds and the separation of the least prime factor.
- Proposition 6's stepping argument, the range `m < x^{1−u₂}` of its fundamental-lemma terms, and its coefficients: in the second case `r` sits in the factor bounded through the zeros, so `c_r` must be the indicator of a region.
- §6's signs, and the sharp rule.

**The Lean map** (stack modules that exist, and what is missing).

- In the stack:
  - (H1): `Eis.LFunction_ne_zero_of_re_gt`;
  - orthogonality over characters: `LinnikHybrid.sum_chars_norm_sq_le`, and the hybrid mean value `LinnikHybrid.mean_value_chars`;
  - the density machinery of rounds 524–527: `Linnik.CharDensity`, proved by `LinnikTwelve.charDensity_twelve_fifths` with the uniform exponent `12/5 + 54ε`. It counts characters, not zeros, at every height;
  - the explicit-formula deduction `Linnik.linnik_of_charDensity`.
- Missing:
  - Lemma 1 (contour shifts for smooth prime sums inside zero-free rectangles of height `x^ε`);
  - Lemma 2 (it needs zero counts, or a smoothing that keeps the heights below `x^ε`, where a count of characters suffices);
  - Huxley's bound `3(1 − σ)/(3σ − 1)` for each `σ` in `[3/4, 11/12]`. Round 527 proves the uniform `12/5` on that range with one choice of its parameters; Huxley's curve needs a choice that depends on `σ`;
  - Buchstab's identity, the fundamental lemma, Harman's fundamental theorem, and the asymptotics of rough numbers;
  - a kernel-checked bound for the loss. At `L = 2.32` the certificate needs 434 cells of depth 2 and 473 of depth 4, and every bound rests on an enclosure of `ω` on intervals of width `2^{−16}`. Round 579's review counted 518650 of them in a scratch run, up to the argument `8.914`.

**Literature.** IDEAS.md G19 records the literature check of round 580.
