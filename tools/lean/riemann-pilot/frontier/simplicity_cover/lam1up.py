"""Certified upper bounds on lambda_1 (even sector) at delta' = node - 1e-9 < node (valid at the node since
lambda_1 is nonincreasing in the support): ball Rayleigh quotient of the cosine minimiser (weil_prime_gram)."""
import sys, json
import os; sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "../../../../research"))
from weil_prime_gram import certify
node, K, prec = float(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
st = certify(node - 1e-9, K, prec)
st.pop("coeffs")
st["node_delta"] = node
print(json.dumps(st), flush=True)
