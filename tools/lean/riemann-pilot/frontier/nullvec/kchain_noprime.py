#!/usr/bin/env python3
"""Round 86: the window chain with the prime terms removed (archimedean Gamma part + pole only).
Same as kchain.py; weil_prime_gram.prime_powers is replaced by an empty list. Usage as kchain.py."""
import sys, runpy
import nullvec_fast  # noqa: path
import weil_prime_gram
weil_prime_gram.prime_powers = lambda N: []
sys.argv = ["kchain.py"] + sys.argv[1:]
runpy.run_path("kchain.py", run_name="__main__")
