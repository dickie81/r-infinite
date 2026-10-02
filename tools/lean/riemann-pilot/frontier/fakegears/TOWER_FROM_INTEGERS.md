# The lattice ball tower from integers and primes (round 183)

The goal is to build the tower of lattice balls ℤ^d, for every d, using only whole numbers and primes, with no geometry put in. There are four steps, each classical. `ktower.py` / `ktower_results.json` check them numerically.

## Step 1. Integers give the balls (counting)

- **Input.** Only the list of squares, `0, 1, 4, 9, …`. Form `θ(q) = Σ_k q^{k²}`.
- **Construction.** The coefficient of `q^n` in `θ(q)^d` is the number of ways to write `n` as a sum of `d` squares, i.e. the teeth on shell `n` of the d-dimensional lattice ball. The cumulative sum `N_d(x)` counts every point of the ball `|x|² ≤ x`.
- **Result.** `N_d(x)/x^{d/2}` tends to the ball volume `π^{d/2}/Γ(d/2+1)`. Averaged over `x ∈ [2·10⁴, 4·10⁴]`:

| d | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 |
|---|---|---|---|---|---|---|---|---|---|---|
| counted | 1.99999 | 3.14165 | 4.18890 | 4.93497 | **5.26402** | 5.16798 | 4.72505 | 4.05899 | 3.29877 | 2.55039 |
| rel. err | 3e-6 | 2e-5 | 3e-5 | 3e-5 | 4e-5 | 5e-5 | 6e-5 | 7e-5 | 8e-5 | 9e-5 |

- The remaining error is the averaging window, not the lumps.
- **Straight from the counts:**
  - The ball volume is largest at **d = 5**.
  - The sphere area `S_{d−1} = d·V_d` is largest at **d = 7**, i.e. on the sphere `S⁶`.
  - These match Part 0's `d_V = 5` and `d_max = 6` for `Ω_d = |S^d|` (`src/cascade-series-part0.tex`, proof of `thm:tower`).
  - Only these two selections are reproduced here. The thresholds 19 and 217 need Part 0's `p(d)` and the constants `½ ln π` and `√π`, which I have not computed from counts.

## Step 2. The integers' fine↔coarse symmetry gives every real dimension and the Gamma function

- **Poisson summation on ℤ** gives `θ(e^{−πt}) = t^{−1/2} θ(e^{−π/t})`: a fine grid of light points equals a coarse grid of heavy points.
- **Every real d at once.** Raising to any real power `d` gives `t^{d/2}θ(e^{−πt})^d → 1` as `t → 0`. Checked to 12 digits for `d = 0.5, 2.5, 7.2569…, 19, 217`.
- **Where the Gamma function comes from.** `θ^d` is the counts averaged over all scales with weight `e^{−πtn}` (a Laplace transform). Undoing that averaging for a count that grows like `x^{d/2}` produces exactly `Γ(d/2+1)`, by Karamata's Tauberian theorem.
  - So the Gamma function, and with it the whole continuous tower `V_d`, `S_{d−1}`, is **forced by the integers' Poisson symmetry**, for every real `d`.

## Step 3. Primes give the lumps

- Round 182: the teeth on each shell equal the smooth tower times a product of local factors, one per prime (Siegel):
  `r_d(n) = (S_{d−1}/2)·n^{d/2−1} · Π_p δ_p(n)`.
- Each `δ_p` comes from counting sums of squares modulo powers of `p`, which is prime `p`'s own small ball.
- This is exact for `d ≤ 8`. From `d = 9` a non-local correction (a cusp form) appears.

## Step 4. Primes plus the integers' symmetry force the tower as a single object

- **The primes alone** give `ζ(s) = Π_p (1 − p^{−s})^{−1}`.
- **Ask which extra factor `G(s)` makes `G(s)ζ(s)` symmetric under `s ↔ 1 − s`** (the integers' Poisson symmetry). Require three things:
  1. `G` has no zeros;
  2. `Gζ` has poles only at `0` and `1`;
  3. `G` grows at most like `e^{|s|^{1+ε}}` (order ≤ 1).
- **Then `G` is unique up to a constant.**
  - Let `G₀ = π^{−s/2}Γ(s/2)`. The ratio `h = G/G₀` is entire and zero-free (conditions 1–2), of order ≤ 1 (condition 3), and satisfies `h(s) = h(1 − s)`.
  - Order ≤ 1 with no zeros gives `h = e^{a + bs}`. The symmetry then forces `b = 0`.
- **And `G₀(s) = 2/S_{s−1}`** (round 142): the forced factor is the reciprocal sphere area, continued in the dimension.
- **Reading.** Given the primes and the integers' symmetry, the continuous ball tower is not an extra input. It is the one factor that completes ζ.

## What is and isn't derived

- **Derived.**
  - From integers alone: the continuous tower `V_d`, `S_{d−1}`, and the selections `d = 5` (volume) and `S⁶` (sphere area).
  - From primes: the lumps, exactly for `d ≤ 8`.
  - From primes and integers together: the tower is the unique completing factor.
- **Not derived here.**
  - Part 0's thresholds `d₁ = 19` and `d₂ = 217`.
  - Part 0's "no fifth dimension" claim, which is about a class of procedures and needs its own definition.
  - The 1-2-4-8 and 9 selections of the lattice picture (round 182), which differ from the cascade's.
- **Check 4.** Classical: Gauss's lattice counting; Poisson and Jacobi for θ; Karamata; Siegel; the uniqueness of the completing Gamma factor, which is standard in the style of Hamburger's theorem. New here, as numerics only: the explicit check that counting integer points reproduces the tower and its `d = 5` and `S⁶` maxima.
- **Check 8.** The cascade hypothesis is not used anywhere. The comparison with Part 0's `d_V`, `d_max` is a cross-check.

**Bearing on RH:** none. Step 4 is the functional equation, which holds whether or not RH does.
