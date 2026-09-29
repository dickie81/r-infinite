# Pre-registration: Karatsuba step inequalities (round 197)

Written before running `kkaratsuba.py`. These are theorems (spec Steps A–C), so any violation
means the spec is wrong.
- K1: `T ≤ 2·T_BB + 16·C(s+k,k)²·G`.
- K2: `G ≤ p^{2s−1}·Σ_a G_a`.
- K3: `G_a ≤ k!·P^k·p^{k(k−1)/2}·J_s(Q)` for every `a`.
Cases: `k = 2`, `p = 3`, `P ∈ {3,…,9}`, `s ∈ {1,2}`.
Exploratory: the slack factor in K3; whether T_BB or G dominates K1.
