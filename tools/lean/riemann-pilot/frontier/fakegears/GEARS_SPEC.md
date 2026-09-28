# The gear model, locked down (round 180)

What rounds 175–179 have actually computed, stated as a model.

- **(F)** marks what is forced by the arithmetic: nothing else would reproduce ζ.
- **(C)** marks a picture I chose, which could be swapped out without changing any computed number.
- **[R-n]** gives the round where the item was computed or checked.

## 1. The floor

- **(F)** The floor is the number line with one mark at each whole number: ℤ in 1D, ℤ[i] (the square grid) in 2D, the Lipschitz/Hurwitz quaternion grid in 4D.
- **(F)** The floor comes first and the wheels are derived from it. Asking for exactly one mark per whole number and building wheels greedily yields exactly the primes [R-179, S1].

## 2. The wheels (the "spheres")

- **(F) 1D.** One wheel per prime `p`, circumference `p`, carrying **one tooth**.
- **(F) 2D.** One wheel per Gaussian prime `π`, radius `|π| = √p`, one tooth.
  - Each `p ≡ 1 (mod 4)` gives two wheels, tilted at angles `±arg π`.
  - Each `p ≡ 3 (mod 4)` gives one wheel of radius `p`.
  - `2` gives one wheel.
- **(F) 4D.** Each prime `p` gives `p + 1` wheels of radius `√p` (the Hurwitz primes of norm `p`, up to units), each tilted in its own 4D direction.
- **(F) 8D.** The octonions are not associative, so rolling wheel A then wheel B differs from rolling B then A in a way that is not merely an order swap. Factorisation into primes is not unique, and the wheel model has no clean Euler product.

## 3. How a wheel rolls

- **(F) Rolling = multiplication, and multiplication = rotation + scaling.**
  - Multiplying by a Gaussian integer `π` rotates the plane by `arg π` and scales it by `√p`.
  - Multiplying by a quaternion is a 4D rotation plus a scaling.
- **(F) The path is straight.** Rolling one wheel repeatedly gives `π, π², π³, …`, which is a log-spiral: angle `k·arg π`, radius `p^{k/2}`. In log-polar coordinates that is a straight line. In 1D it is simply `p, p², p³, …`.
- **(F) The prints.** A wheel's single tooth, rolled along the floor, prints the lattice `π·ℤ[i]`: a square grid rotated by `arg π`, with spacing `√p`. In 1D the prints are the multiples of `p`.

## 4. Why the wheels touch the floor many times, and each other never

- **(F)** Each wheel touches the floor at one point at a time. It prints a mark once per revolution, so there is one mark every `p`.
- **(F)** Wheels do not touch each other. Two wheels' marks land on the same floor point at their common multiples: every `pq` in 1D, which is the Chinese remainder theorem [R-178 discussion]. A floor point `n` is hit by every wheel dividing `n`, as many times as that wheel's power in `n`.
- **(F)** The score of point `n` is `μ(n)`: `±1` for an odd/even number of distinct wheels, `0` if one wheel hits twice. Summing the scores gives the slippage `M(x)` [R-176].

## 5. The second picture: every wheel spinning at once

- **(F)** Read at height `t`, wheel `p` sits at angle `t·log p`. All wheels turn together at constant speeds `log p`.
- **(F) Straight but random-looking.** The joint position moves in a **straight line** on an infinite-dimensional torus (the Bohr torus). The path is deterministic, not Brownian.
  - The speeds `log p` have no common rhythm (unique factorisation), so the line never closes and passes near every configuration (Kronecker–Weyl).
  - Seen from any finite set of wheels, the positions are statistically indistinguishable from independent random angles (Bohr–Jessen).
- **(F) On the critical line.** The accumulated wobble behaves like a random walk whose "time" is `½ log log t` (Selberg's central limit theorem). So it is a straight path that *looks like* Brownian motion, very slowly.
- **(C)** The word "Brownian" is a description only. No randomness is put in anywhere.

## 6. What the tones and volumes are

- **(F)** The drift `ψ(x) − x` and the slippage `M(x)` are chords whose pitches are exactly ζ's zero heights `γ` [R-175, R-176].
- **(F)** A tone's volume is `2/|ρζ′(ρ)|`: a hypotenuse `|ρ| = √(¼ + γ²)`, times a slope set by the neighbouring zeros' gaps [R-177].

## 7. What is not in the model

- **(C)** The wheels are wheels, not literal balls rolling on balls. The "ball" is the norm shell `|z|² = n`, and the wheels are the primes of that grid.
- **Nothing in 1–6 is new mathematics.** It is Euclid, Gauss, Hurwitz, Bohr, Selberg and the explicit formula, arranged as a mechanism.
- **Where RH sits.** RH is a statement about the size of the random-looking wobble in §5 along the straight path at `σ = ½`: whether it stays within `x^{½+ε}`.
