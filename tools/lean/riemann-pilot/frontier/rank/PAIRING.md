# The release's pairing through theta components

Side-branch note, 2026-10-22, on branch `claude/latest-commit-branch-ik1pj3`. It follows `CUBIC.md` in this directory. It is not a README round, and it adds no Lean. The numbers below come from the gate script `pairing_gates.py` and the committed record `sextic_dual.json` (section 7), or are quoted from the sources cited.

**The question.** The owner's instruction: "Keep digging". After README rounds 503–505 one input of the release's low side is open in the register: "a bound for the pairing of `A_m` with `B_m` below Cauchy–Schwarz" (STRUCTURAL-REVIEW §6, the bullets of rounds 504 and 505). `CUBIC.md` found the Möbius sum on the theta component of the cubic route's dual. This note asks what the theta components of the release's two factors carry.

**Summary.**
1. **The completed rows are Möbius-weighted sextic Gauss sums.** By the release's eq. (signal), the part of the completed row with `n = 1` is a column of conjugate normalized sextic Gauss sums `conj(g(c, m))` at the row `m`, weighted by `μ(c)` and fixed characters (section 1; gate P0).
2. **Theta components.** The Gram bound's exceptional term `(Q/Y′)P_a^{1/6}` is the energy of the additive polynomial's sextic theta component `A_θ` (Xu–Sang's main term; rounds 496 and 504). In the theta reading, the completed rows' sextic theta component `B_θ` carries the Möbius sum of the target. The slots multiply it by the release's own normalizer `Z^{ℓ/6}A_T(Z)`. The pairing of the two has exactly the exponent of the release's principal signal, `C(β) = β − 5/6 + l_x/3 + ℓ/6`, identically in the geometry (gate P1).
3. **The boundary is the completed rows' theta energy against their energy bound.** The release's low bound is `Q^{−1/2}‖A_θ‖‖B‖`. It meets the signal exactly where `‖B_θ‖² = ‖B‖²`, at `β_b = 5/6 − ℓ/6 + M/12 + L/2` (gates P2, P3). The additive polynomial cancels. The formula gives the release's `7/8`, Part I's `11/12`, round 503's `11/12 − ℓ/4` on Sang's slice (and with it round 503's cancellation of `b`), and round 496's `13/15`.
4. **The same template at every order** (identically in `N`; gate P6 checks the orders of `orders.ORDERS`). Round 288's extraction `θ_N(σ)` is exactly where the order-`N` theta component of the family's dual, carrying the Möbius sum, reaches the dual's target `Z²`. For `N = 3` this is `CUBIC.md`'s fixed point; for `N = 6` at `σ = 0` it is the companion's `11/12`. In this reading, a route yields a half-plane when it proves the energy bound without using the Möbius sum: the companion through absorption into cubic Gauss sums, the release through its completed reflection. It is a fixed point when the energy bound needs the Möbius sum, as on the cubic route.
5. **What a pairing bound below Cauchy–Schwarz would have to do.** Cauchy–Schwarz is attained, up to constants, when `B` lies on the theta direction with its whole energy. A zero at the boundary produces that configuration; beyond the boundary the energy bound fails, which is the release's contradiction. The release's high side ties the probe to the signal. In this reading, a pairing bound below the release's bounds the projection of `B` on the theta direction below `‖B‖`. That is the amplified Möbius sum bounded below the boundary, so the bound would give the half-plane directly. A split `A = A_θ + A_rest` with an input half-plane returns its input (gate P4). The open input is circular in the sense of CLAUDE.md Check 9(c).
6. **Numerics** (section 5). A modulus sees only the moduli of its unit class, exactly (gate P5). With that taken into account, the dual projections of primes, of a multiplicative sign and of the Möbius function follow the weight-one projection at fixed norm, in the regime of the release's completed rows (rows fewer than moduli, `Z ≤ 8·10⁴`) and at `H = Z` (`Z ≤ 8·10⁴`) (gates S1–S4). The profile in the norm is not `N(c)^{−1/3}` at these sizes (gate S5). The additive polynomial's own regime, rows far beyond the moduli, is out of reach at these sizes (gate S6); for `A_θ` the note relies on Xu–Sang's theorem.
7. **The levers left in this probe** are the amplifier `ℓ`, the row count `M` and the row-norm loss `L`. Rounds 501–506 bound `ℓ` from the high side; round 500 and the register's slice note treat `M` and `L`.

## 1. The two factors

The release separates its probe exactly (its eq. `low-separated`):

> `I_\eta(X,Y,Z)=\frac{Q^{-1/2}}{2\pi} \sum_{\sigma\in T}\int_{\mathbb R}\widehat W_0(iv) \sum_{m\ne0}\Omega(q_m/Q)\xi(m)(q_m/Q)^{-iv} A_{m,\sigma,v}(Y)B_{m,\sigma}(Z)\,dv.`

**The additive polynomial** is a column of sextic Gauss sums over the moduli `s` of one ray class:

> `A_{m,\sigma,v}(Y)=\frac1Y\sum_{s\in\sigma} \frac{W_1(q_s/Y)\chi_s(b_*)}{\tau\xi(s)} (q_s/Y)^{-1/2+iv}q_s^{-1/2}g_{\chi_s}(s,-m).`

**The completed row** `B_{m,σ}` is built from the corrected row

> `T_{m,s,\eta}(t)= \sum_{\substack{c\ {\rm sf}\\n}} \gamma_2(c)\overline{\alpha(cn^3)}\Psi_{m,s,\eta}(cn^3) \overline{G(cn^3)}q_c^{-1/2-t}q_n^{-1-3t}.`

Here `Ψ_{m,s,η}(a) = η(a)Ξ(a)^{−1}ℛ(a, s)χ_a(m)`. The release: "the displayed Mellin integral of the corrected row equals `$B_{m,\sigma}(Z)$` throughout that class". Its overview calls it a sum that "averages smoothed cubic-theta Fourier coefficients against these characters and a fixed target `$\eta$`": `γ₂(c)` is the normalized cubic Gauss sum.

**Its terms with `n = 1`.** The release's eq. (signal) reads

> `\gamma_2(c)^3=\mu(c)\alpha(c),\qquad \gamma_1(c)\gamma_2(c)=\mu(c)\alpha(c)G(c),\qquad G(c)=\overline{\chi_c(4)}\gamma_3(c),\quad |G(c)|=1.`

Since `|γ₁(c)| = |α(c)| = 1` at squarefree `c`, it gives `γ₂(c)·conj(α(c))·conj(G(c)) = μ(c)·conj(γ₁(c))`. Write `g(c, m) = q_c^{−1/2} Σ_{v mod c} χ_c(v)e(mv/c)` for the normalized sextic Gauss sum at frequency `m`. Then `conj(γ₁(c))χ_c(m) = conj(g(c, m))`, both sides vanishing when `(c, m) ≠ 1`. So the terms with `n = 1` are

`Σ_c μ(c)η(c)Ξ(c)^{−1}ℛ(c, s)·conj(g(c, m))·q_c^{−1/2−t}`:

a Möbius-weighted, twisted column of conjugate sextic Gauss sums at the row `m`. This is the companion's absorption, `ORDER-RANK.md`'s identity A3, read backwards. The terms with `n ≠ 1` carry `q_n^{−1−3t}`. In the high representation they become the families with `l ≥ 1` in the release's local factor `P_p` (its eq. `local-P`).

**Gate P0.** In the pilot's own Gauss sums (`composite.py`, `periods.c`), `γ₂·conj(α)·conj(G) = μ·conj(γ₁)` holds with `G = conj(χ_c(4))γ₃` at all 700 squarefree primary moduli of norm `≤ 2500` (error `6·10⁻¹²`), together with the two identities of eq. (signal). So the pilot's conventions agree with the release's.

## 2. Theta components and the boundary

**The sextic theta function.** By Kubota, `Σ_c g(c, m)N(c)^{−w}` has its pole at `w = 2/3` for normalized sextic Gauss sums, with residue proportional to the sextic theta coefficient `ρ(m)`. Its energy is `Σ_{q_m ≤ Q} |ρ(m)|² ≍ Q^{5/6}`.

**`A_θ`.** A column of Gauss sums over moduli of size `Y` has the theta component `Y^{−1/3}ρ_A(m)`. Here `ρ_A` is the theta function that `A`'s ray class and twists select: round 504's class `r ≡ a − 1` at the primes of `S`, and round 505's classes at `2` and `3`. Its energy is `Y^{−2/3}Q^{5/6} = (Q/Y)P_a^{1/6}`. This is the Gram bound's exceptional term, which the release's proof gets from the exceptional frequencies: "This gives the term `$(Q/Y')P_a^{1/6}Z^\epsilon$`." It is Xu–Sang's main term, quoted in README round 496: "Their sixth-power structure leaves a contribution of scale `\((A/B)Y^{1/6}=A^{5/6}B^{-2/3}\)`."

**`B_θ` and its mass.** The mass rule: a weighted column `Σ_c w(c)·g_N(c, ·)` of order-`N` Gauss sums has the theta component `ρ_N·Σ_c w(c)N(c)^{−(1/2 − 1/N)}`, the sum over the moduli prime to the row. `CUBIC.md` measured it at `N = 3`, where the exponent is `1/6`. At `N = 6` the exponent is `1/3`, and section 5 tests the rule numerically. With the weights of section 1, `w(c) = μ(c)ν(c)q_c^{−1/2}V(q_c/Z)`, the mass is

`Σ_c μ(c)ν(c)q_c^{−5/6}V(q_c/Z) = (1/2πi)∫ Z^tΦ(t) / L^S(t + 5/6, ν) dt`.

That is the release's signal variable. The release sets "`$x=t+1-z$` after Mellin inversion", and the principal residue sits at `z = 1/6`, so `x = t + 5/6`.

**The slots.** A marked slot prime `p` enters `B` with `conj(η(p))`, and the Möbius weight of `c = pc′` gives `μ(p)η(p) = −η(p)`. So in this reading each slot multiplies the mass by `−Σ_{p∈𝒫_i(Z)} W_i(q_p/P_i)q_p^{−5/6}`; the fixed phases at the slot primes are not tracked. The release's own computation gives this factor at the principal point. It finds "`\(\mathcal B_p=-1+O(q_p^{-7/8})\)`" at each slot prime, so each slot contributes `−S_i(Z)` up to `1 + O(P_i^{−7/8})`, with "`S_i(Z)=\sum_{p\in\mathcal P_i(Z)}W_i(q_p/P_i)q_p^{-5/6}`". The product is its normalizer: "`A_T(Z)=(-1)^K Z^{-\ell/6}\prod_{i=1}^K S_i(Z)`". The energy bound does not grow with the slots. Lemma `lem:probe-row-norm`: "The bound is uniform in the fixed rescaled tuple and has no loss depending on the mesh of the surviving slots." Per slot of primes of norm about `P`, the mass squared grows by about `P^{1/3}/log P` per unit of diagonal energy.

**The pairing (gate P1).** `Q^{−1/2}⟨A_θ, B_θ⟩` has the exponent `−M/2 − l_y/3 + 5M/6 + (β − 5/6 + ℓ/6)` at a zero of real part `β`. This equals `C(β) = l_x/2 + β − 1 + h/6`, with `h = 1 − l_x + ℓ`, identically. Its coefficients in `(l_x, l_y)` are `(1/3, 0)`, the high side's `X^{1/2−z}Y^{w−1}` at `(w, z) = (1, 1/6)`. The release: "At the double residue the outside power is `X^{1/3}Z^{s-5/6}Z^{\ell/6}=Z^{C(s)}`". Gate P1 checks the identity at 2000 random rational geometries and at the release's two.

**The low bound (gate P2).** The release's proof of Proposition `prop:probe-low` bounds a tuple by "`Q^{-1/2}\bigl[(Q/Y')P_a^{1/6}\bigr]^{1/2} \bigl[Z^{M'}\bigr]^{1/2}`". That is `Q^{−1/2}‖A_θ‖·‖B‖`, with `‖B‖²` at the row count `Z^{M+L}`. Its exponent is `l_x/2 + b/12 + L/2`: `3/16 = C(7/8)` at the release's geometry ("`C_{\mathrm{II}}(7/8)=3/16=l_x/2+b/12`"), and `1/4` in Part I.

**The boundary (gate P3).** The pairing meets the low bound exactly where `‖B_θ‖² = ‖B‖²`:

`β_b = 5/6 − ℓ/6 + M/12 + L/2`.

`‖A_θ‖` enters both sides and cancels, so the boundary depends on the geometry only through `M = l_x + l_y`, `ℓ` and `L`.

| geometry | `β_b` | where it is recorded |
|---|---|---|
| the release, `(l_x, l_y, ℓ) = (17/48, 23/48, 1/6)`, `L = 0` | `7/8` | its theorem |
| Part I, `(1/2, 1/2, 0)` | `11/12` | Theorem `thm:eleven-twelfths` |
| Sang's slice `M + ℓ = 1`, `ℓ ≤ 1/5` | `11/12 − ℓ/4` | README round 503 |
| that slice with Sang's loss `L = (5ℓ − 1)₊/4`, least over `ℓ` | `13/15` at `ℓ = 1/5` | README round 496, W6b |

The formula equals round 503's `s₀ = 5/6 + l_x/6 − ℓ/6 + θb/2` at `θ = 1/6` (plus `L/2`) identically.

**What this explains.**
- **Round 503's cancellation of `b`.** On Sang's slice the boundary does not depend on `b`. In this reading the reason is that `A` enters only as the detector `‖A_θ‖`, which cancels.
- **Round 504's gate X5.** The same characters keep the exceptional term and the principal residue at `z = 1/6`. In this reading both are `A_θ`: when the choice of `ξ` removes `A_θ`, the theta–theta pairing, which is the signal, goes with it.
- **The exceptional term is the detector, not a loss.** Without it the bound would be `β_rest = 5/6 − ℓ/6 + l_x/6 + L/2 = β_b − b/12` (`83/96` at the release's geometry; gate P4), round 503's "lowers it by `b/12`". But `‖A‖ ≥ ‖A_θ‖` (rounds 504–505), and the term is what lets the probe see the signal.

## 3. The same template at every order

`ORDER-RANK.md`'s families are `A_Z(u) = Σ μ(𝔞)(u/𝔞)_N W(N𝔞/Z)`, with the extraction `θ_N(σ) = (2N − 1 + (N − 1)σ)/(2N)`. Their dual at block `σ` has rows `N(k) ≤ H = Z^{1−σ}` and the target `Z^{2+ε}`. By the mass rule, its coefficients `μ(n)G_N(n)` give the dual an order-`N` theta component. Its energy is `H^{1−1/N}|M_N(Z)|²`, with the Möbius mass `M_N(Z) = Σ_{N(n)≤Z} μ(n)N(n)^{−(1/2−1/N)}`, of size `Z^{θ−1/2+1/N}` at a zero of real part `θ`.

**Gate P6.** The component reaches `Z²` exactly at `θ = θ_N(σ)`. This holds for every `N` in `orders.ORDERS` and 121 values of `σ`, against `orders.theta`, which `ORDER-RANK.md` derives from the family's `N`-th powers. The agreement is what Poisson duality suggests. The family's `N`-th powers `u = b^N` carry the Möbius sum in the extraction, and on the dual side they correspond to the theta function's expansion. The gate checks the exponents, not the duality. At `N = 3` the gate reproduces `CUBIC.md`'s `component_exponent` and `component_sigma`. At `N = 6` and `σ = 0` it gives `11/12`.

**Reading.** In each of the four settings below, the half-plane is where a theta component carrying the Möbius sum would exhaust an energy budget. The difference between them is how the budget is proved.

| setting | theta component and its mass | the energy budget | outcome |
|---|---|---|---|
| the cubic route (`CUBIC.md`) | cubic, `Σ μ(n)N(n)^{−1/6}` | not proved: within `CUBIC.md`'s section 4 scope, bounding the dual goes through the component | a fixed point, `θ₀ → θ₀` |
| the companion's sextic family | sextic, `Σ μ(n)N(n)^{−1/3}` | absorption to cubic Gauss sums, whose own cubic component has a Grössencharacter mass (`CUBIC.md` §3); degree 2, `σ ≥ 0` in `ORDER-RANK.md`'s model | `θ₆(0) = 11/12` |
| the release, Part I | sextic, `Σ μ(c)η(c)q_c^{−5/6}V` | the completed rows' norm, by the completed reflection, at the row count | `11/12` |
| the release, Part II | the same, times `Z^{ℓ/6}A_T(Z)` | the same norm, uniform in the slots | `7/8` |

This sharpens `CUBIC.md`'s contrast. There, "absorption removes the Möbius function from its dual's theta component". That is true of the sextic dual's cubic theta component. Its sextic theta component keeps the Möbius sum. It is the component through which the absorbed energy bound becomes the half-plane `θ₆(σ)`.

## 4. What a pairing bound below Cauchy–Schwarz would have to do

**The configuration.** Under its contradiction hypothesis the release proves that its probe is its signal up to a power saving. Its continuation criterion: "A direct bound for the sum and a power-saving bound for its difference from that integral imply the required continuation." In the principal row, Lemma `lem:principal-residue-interface` bounds `\frac{\mathscr P_\eta(Z)}{c_SA_\eta(Z)}-f_\eta(Z)` by powers below `Z^{C(β_*)}`.

In the theta reading the probe's main term is `Q^{−1/2}⟨A_θ, B_θ⟩`, and a zero of real part `β` makes `‖B_θ‖²` of size `Q^{5/6}Z^{2(β − 5/6 + ℓ/6)}`. At `β = β_b` that is the energy bound `Z^{M+L}`, and the release's two factor bounds are both attained, up to constants and `Z^ε`:
- `‖A‖` at `‖A_θ‖`, the main term of rounds 504–505;
- `‖B‖` at the row count, its diagonal, with `B_θ` taking the whole of it.

Cauchy–Schwarz is then attained too. Beyond `β_b` the configuration would break the energy bound, which is the release's contradiction in these terms.

**The consequence.** A bound `|Σ_m A_m B_m| ≤ Z^{−δ}‖A‖‖B‖`, for the release's probe at every target, gives the half-plane `β_b − δ` by the release's own argument (round 503's step-by-step reading of the low side). In the theta reading the pairing's main term is `⟨A_θ, B⟩ = ⟨A_θ, B_θ⟩`, the amplified Möbius sum times `‖A_θ‖‖ρ_A‖`. So such a bound is a bound for the projection of `B` on the theta direction below `‖B‖`, that is, for the amplified Möbius sum below the boundary. It contains its conclusion. The release's inputs, `‖A‖` at `‖A_θ‖` and `‖B‖` at its diagonal, do not supply it: both are attained in the aligned configuration. So the register's open input, in this reading, is a bound for the circular signal (Check 9(c)), not an auxiliary one.

**Gate P4 (the split).** Write `A = A_θ + A_rest`, bound `⟨A_θ, B⟩` from an input half-plane `Re s > θ₀`, and bound the rest by the Gram diagonal. The result is `max(θ₀, β_rest)`, with `β_rest = 83/96` at the release's geometry. With the release's `7/8` as input it returns `7/8`. Since its output is `max(θ₀, β_rest)`, the split never returns a half-plane better than its input.

**Scope** (CLAUDE.md Check 9(a)).
- **Exact, gated:** P0 (the completed rows' Gauss-sum form at `n = 1`), P1–P4 (exponent identities) and P6 (the extraction as a theta-energy boundary). P5 is section 5.
- **A reading, not a theorem:**
  - the identification of the low side's pieces with theta components. The exceptional term as `‖A_θ‖²` rests on Xu–Sang's main term and rounds 504–505. The mass of `B_θ` rests on the mass rule, measured at order 3 in `CUBIC.md` and tested at order 6 in section 5.
  - the class bookkeeping (`σ ∈ T`, `θ ∈ T̂`, the Kummer shifts at the primes of `S`), which is not tracked here. Rounds 504–505 track it for the exceptional term and for the residue, and find that the same classes keep both.
  - the terms with `n ≠ 1`, which are not examined.
- **Not excluded:**
  - a bound for the projection of `B` on the theta direction that uses a second representation of it (section 6, attack note 1);
  - a larger amplifier;
  - a lower row count or row-norm loss (the levers of section 6).

## 5. Numerics: the sextic dual projections

`sextic.py` takes the squarefree primary moduli `c` of norm `≤ Z` and every nonzero row `k` of norm `≤ H`. With `R(k) = Σ_n g(n, k)` (weight one) it computes, for each modulus, the off-diagonal row sum of the Gram matrix:

`y(c) = Σ_k conj(R(k))g(c, k) − #{k : (k, c) = 1}`.

Then `<R, R_w> − Σ_c w(c)·diag(c) = Σ_c w(c)y(c)` for any weight `w`, so one pass tests every weight.

**Unit classes (gate P5, exact).** The rows are closed under the six units, and `g(n, εk) = conj(χ_n(ε))g(n, k)`. So `R` splits into orthogonal parts `R_u` by the unit character `u` of the modulus, and a modulus sees only its own class: `y(c)` involves only the moduli `n` with `u(n) = u(c)`. P5 checks this by brute force at norm `≤ 600`.

The prediction is made class by class: `y(c) ≈ N(c)^{−1/3}κ(c)`, with `κ(c) = Σ_{(k,c)=1} e_u(k)/m_u(k)`. Here `e_u(k) = |R_u(k)|² − #{n ∈ u : (n, k) = 1}` and `m_u(k) = Σ_{n∈u, (n,k)=1} N(n)^{−1/3}`. It has no fitted constant: summed over the moduli of a class, both sides equal `Σ_k e_u(k)`.

**Results** (`sextic_stats.py`, recorded in `sextic_dual.json`; `P` is the projection coefficient of a weight on the prediction, and the standard errors come from 400 random-sign draws per Galois orbit):

| `Z` | `H` | rows | weight-one excess | `mixed`: one class / classes | primes `P^prof` | `mixed` `P^prof` | `μ`: `P` / `P^prof` | largest twisted `z^prof` | largest bin deviation |
|---|---|---|---|---|---|---|---|---|---|
| `1·10⁴` | `1000` | 3642 | `+0.748` | `1.630` / `0.986` | `0.986 ± 0.033` | `0.963 ± 0.055` | `1.00` / `0.86 ± 0.18` | `1.76` | `11.7` se |
| `2·10⁴` | `1682` | 6108 | `+0.887` | `1.680` / `0.995` | `0.983 ± 0.023` | `0.972 ± 0.039` | `0.92` / `0.80 ± 0.19` | `2.29` | `9.9` se |
| `4·10⁴` | `2828` | 10278 | `+1.056` | `1.653` / `0.980` | `0.989 ± 0.017` | `0.968 ± 0.026` | `1.22` / `1.04 ± 0.19` | `1.84` | `15.1` se |
| `8·10⁴` | `4757` | 17250 | `+1.284` | `1.674` / `0.998` | `0.995 ± 0.012` | `0.987 ± 0.019` | `1.38` / `1.13 ± 0.18` | `2.25` | `22.3` se |
| `1·10⁴` | `10000` | 36294 | `+0.671` | `1.475` / `0.996` | `0.989 ± 0.015` | `0.993 ± 0.027` | `0.76` / `0.90 ± 0.11` | `2.15` | `7.5` se |
| `2·10⁴` | `20000` | 72564 | `+0.782` | `1.422` / `1.013` | `0.991 ± 0.011` | `1.010 ± 0.019` | `0.80` / `0.95 ± 0.11` | `1.28` | `15.2` se |
| `4·10⁴` | `40000` | 145050 | `+0.902` | `1.415` / `1.021` | `0.995 ± 0.008` | `1.019 ± 0.012` | `0.79` / `0.95 ± 0.10` | `1.54` | `22.0` se |
| `8·10⁴` | `80000` | 290238 | `+1.044` | `1.443` / `1.010` | `0.990 ± 0.005` | `1.010 ± 0.008` | `0.67` / `0.81 ± 0.10` | `2.76` | `25.4` se |

- **S1, the unit classes are needed.** Against a one-class prediction the sign weight `mixed` projects at `1.42`–`1.68`, because it correlates with `χ_c(−1)`. Against the class prediction it projects within `0.03` of `1`.
- **S5, the profile in the norm is not `N(c)^{−1/3}`.** In every run some norm bin with at least 20 moduli has a mean ratio `y(c)/(N(c)^{−1/3}κ(c))` more than 4 standard errors from `1` (between `7.5` and `25.4`). The pattern depends on `H/Z`. With rows fewer than moduli, the mid-sized moduli project up to about `1.7` times the prediction and the largest about `0.9` times it. At `H = Z` the smallest moduli project below it. Below, `P^prof` multiplies the prediction by the weight-one ratio of each norm bin (16 bins). It asks whether `y(c)` depends on `c` only through its norm and unit class.
- **S2–S4, arithmetic at fixed norm.** Primes, the sign and the Möbius function follow the weight-one profile in every run. The Möbius function's `P^prof` lies between `0.80 ± 0.19` and `1.13 ± 0.18`, within `1.9` standard errors of `1` in every run. At the largest `Z` of each regime it is `6.2` (rows fewer than moduli) and `8.1` (`H = Z`) standard errors from `0`. For the twisted weights `μη` and `η`, the characters are:
  - ray classes modulo split primes of norm 7, 13, 19 and 31, of orders 2 to 12, including 4, 5, 9 and 12, which do not divide 6;
  - the infinity types `α^j`;
  - the Kummer characters `χ_c(2)` and `χ_c(λ)`.

  Their deviations are within `2.8` null standard deviations. Their masses are small, so these tests have little power.
- **S6, the additive polynomial's regime is not reached.** With rows far beyond the moduli, `H = 100Z` at `Z = 10³` and `2·10³`, inside Xu–Sang's range `B^{16/11} < A < B²`, the weight-one excess is `+0.0004` and `+0.026` of the diagonal. Their asymptotic is not visible at these sizes, so these runs say nothing about `A_θ`. For it the note relies on Xu–Sang's theorem and rounds 504–505.

**Reading.** At these sizes the sextic dual projections behave as the mass rule needs: linear in the weight at fixed norm and unit class, Möbius weight included. The profile in the norm is a smooth function of `N(c)`, so it changes the smoothing of the Möbius sum, not the zeros that govern it. A sharper test, like `CUBIC.md`'s T4, would fit the component with the theta coefficients themselves. At order 6 their values at squarefree indices are not available in the sources surveyed on this branch (`CUBIC.md`, section 5). At order 3, where they are, T4 gave `0.990 ± 0.049`.

## 6. Outcome, register entry and signals

**Outcome, scoped.** Read through sextic theta components, the release's low side is an amplified energy bound applied to the theta component of the completed rows. Its boundary `β_b = 5/6 − ℓ/6 + M/12 + L/2` is where that component, carrying the Möbius sum of the target and amplified by the slots, would exhaust the completed rows' energy bound. The additive polynomial is the detector and cancels. Within section 4's scope, the open input "a bound for the pairing of `A_m` with `B_m` below Cauchy–Schwarz" is a bound for that component below the energy bound. That is the amplified Möbius sum below the boundary: the half-plane itself.

**Register** (CLAUDE.md Check 9(b)). This note adds a bullet to the sub-entry "Below `7/8` in the release's exponent comparison" in STRUCTURAL-REVIEW §6, and markers on the open items that name the pairing. The target `X`, under the note's reading: **the completed rows' sextic theta projection below their energy bound**, `‖P_{ρ_A}B‖² ≤ Z^{M+L−2δ}`.
- **Socket:** Lemma `lem:probe-row-norm`'s place in Proposition `prop:probe-low`. In this directory, `pairing_gates.boundary`: a saving `δ` on the projection gives `β_b − δ`.
- **Attack notes**, none attempted:
  1. **A second representation of the projection.** The release bounds the energy of `B` through its completed reflection (Proposition `prop:completed-reflection`). Pushed through that reflection, the projection `⟨ρ_A, B⟩` becomes a pairing of the reflected row with a reflected theta function. Whether that pairing can be bounded independently of the Möbius sum is not examined. If it can, it is an auxiliary signal with two representations, as "Signals, not just criteria" asks.
  2. **A larger amplifier at no energy cost.** The slots gain about `P^{1/3}/log P` in squared mass per unit of energy per slot. The high side bounds `ℓ` (rounds 501–506). Other amplifiers, for instance composite slots or slots resonating with `η`, are not examined.
  3. **The energy bound's geometry.** Leaving the slice `M + ℓ = 1`, or lowering the loss `L`, moves `β_b` directly. This is the register's slice note and round 500's crossing cost.

  Round 506's note on Hamdar's cube/residue cancellation gets a reply in this reading. The release's high side makes the probe its signal up to a power saving, so a cancellation in the pairing below the signal is excluded in the configuration that matters.

**Signals** (CLAUDE.md Check 9(c)).
- **The pairing's theta part** is the probe's principal signal. As a target to bound it is circular.
- **The probe itself stays auxiliary**, as round 496 recorded. Its direct estimate (the Gram bound and the completed rows' energy) does not use the zeros.
- **The numerics** of section 5 test the form of the components. They are not evidence about zeros: at these sizes the Möbius sums are small because the zeros are, numerically, on the line.

**Markers** on this branch's earlier notes:
- `CUBIC.md`, on its contrast with the sextic family (section 3 here);
- `ORDER-RANK.md`, on the extraction exponent (gate P6).

## 7. Reproduce

From this directory:

```
python3 pairing_gates.py   # gates P0-P6 (exact; P0 and P5 compile periods.c into a temporary directory) and S1-S6 on sextic_dual.json
```

To regenerate `sextic_dual.json` (the prime data to norm `8·10⁴` suffice):

```
gcc -O2 -o periods periods.c -lm
./periods w 80000 > periods_w_8e4.txt
mkdir -p out
python3 sextic.py periods_w_8e4.txt out 10000:1000 20000:1682 40000:2828 80000:4757 10000 20000 40000 80000 1000:100000 2000:200000   # about 70 min
python3 sextic_stats.py out sextic_dual.json 10000_H1000 20000_H1682 40000_H2828 80000_H4757 10000 20000 40000 80000 1000_H100000 2000_H200000
```

`sextic.py` writes one `.npz` per run (`Z:H`, with `H = Z` when omitted). `sextic_stats.py` reduces them to the record.

## Check 4 and bearing on RH

**Check 4.**
- **Acknowledged:**
  - the exceptional term as a main term (Xu–Sang; rounds 496 and 503–505);
  - round 503's step-by-step low side, with its `11/12 − ℓ/4` and its cancellation of `b`;
  - round 504's gate X5;
  - round 496's cap `13/15`;
  - round 506's note on Hamdar's cancellation;
  - `CUBIC.md`'s mass rule and fixed point;
  - `ORDER-RANK.md`'s absorption identities and extraction.
- **New here:**
  - the completed rows as Möbius-weighted conjugate sextic Gauss sums, from eq. (signal), checked in the pilot's Gauss sums (P0);
  - the theta reading of the release's low side, with the pairing's exponent equal to the signal's (P1);
  - the boundary as theta energy against the energy bound, independent of the additive polynomial, with its four reproductions (P2, P3);
  - the split's fixed point (P4);
  - the extraction at every order as a theta-energy boundary, and the corrected reading of `CUBIC.md`'s sextic contrast (P6);
  - the unit-class orthogonality of the dual projections (P5) and the sextic dual numerics (S1–S6);
  - the reading of the register's open pairing input as a bound for the circular signal.

**Bearing on RH: none.** The note reads the structure of a route to a zero-free half-plane and records where its remaining input stands. It gains or verifies no constraint on zeros.
