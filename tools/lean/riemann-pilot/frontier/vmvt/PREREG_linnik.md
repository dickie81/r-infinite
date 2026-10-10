# Pre-registration: Linnik's lemma (round 196)

Written before running `klinnik.py`.

For prime p > k, residues a (distinct mod p), and targets c:
N(a, c) = #{x ∈ [0,p^k)^k : x ≡ a (mod p), Σ x_i^j ≡ c_j (mod p^j), j = 1..k}.

- L1 (theorem `VinoPadic.linnik`): max over a, c of N(a, c) ≤ p^{k(k−1)/2}.
  A violation would mean the Lean statement is not what the code computes.
- L2 (exploratory): the bound is attained (max = p^{k(k−1)/2}), since for p > k the map to
  residues mod p^k should hit each admissible target exactly once.
- L3 (exploratory): with repeated residues mod p the rigidity fails, and N can exceed the bound
  (e.g. a = (1, 1)).
Cases: (p, k) = (3, 2), (5, 2), (7, 2), (5, 3).
