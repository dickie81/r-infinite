

# Round 236: convergence test on the round-235 sweep (subagent, per protocol) — NOT CONVERGED: 1 minor + 1 cosmetic; swept

**Reviewer's batteries:** manifest precheck no-op; the verifier live (REUSED, 15/15); its own probes — a needle mangle (g14 alone) and the decisive F235-1 mechanism observed live (an interior-corrupted zext chunk → the consolidated load prints RECOMPUTING, no stale reuse possible); two no-edit key computations (the clean key matches the committed filename; a corrupted extension moves it); tower by byte-identity (only the TOP changed since the recorded 16/16) with the TOP live. Every round-235 disposition verified at its locus against data; the eighth-catch hunt over all 24 ckpt_key.load sites came back empty at the checkpoint level.

**The finding, lead-verified and accepted:** **F236-1 minor** — floor_probe.py's docstring claimed "EVERY stage input in the key" while its own runs are intent-keyed (the disclosed attack-run status), contradicting the sibling prose the round-235 sweep wrote. Swept: the quantifier struck at the locus with the intent-keyed status disclosed and the landing's content-keyed re-keying cited. **C236-1 cosmetic** (docstring line wraps) swept in the same commit.

**Sweep battery:** the floor_probe.py docstring edit self-invalidated every family keying its sha (the content-addressing tax, paid in full); full stage recompute, every pin reproduced, 15/15; probes (b)/(c) live (REUSED + g1 alone; census revert → g13+g14); reachability sweep clean; ancestors byte-identical to the recorded TOWER PASS 16/16.

**Trajectory: 1bg landed → 234: 0M+5m+4c (swept) → 235: 5m+2c (swept) → 236 NOT CONVERGED 1m+1c (swept d5842f5 + this commit). Convergence round 237 next; Theorem 1bg certification pends it.**
