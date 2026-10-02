"""Round 123 scoping: relaxation with primes (diagonal in circle modes) + pole, orthonormalised (option 2).
bound(a, N) = kappa' + lambda_min(L^T S L), G = L L^T (Gram of cosh(t/2), cos(pi k t/4a), k = 0..N).
psi_m >= Cin(pi m/2) + a(1 - 2 sin(pi m/2)/(pi m)) - err(a);  tail tau' = Cin(pi(N+1)/2) - err - 2 sum Lambda/sqrt n."""
import mpmath as mp, sys
mp.mp.dps = 60
def err(a): return a**2/6 + a**3/3 + a**4/200 + a**5/48
def Cin(x): return mp.euler + mp.log(x) - mp.ci(x)
def lam(n):
    for p in (2, 3, 5, 7):
        k = 0; m = n
        while m % p == 0: m //= p; k += 1
        if m == 1 and k > 0: return mp.log(p)
    return mp.mpf(0)
EXACT = False
def psi_exact(a, m):
    w = mp.pi*m/(4*a); mp.mp.dps = 30
    return mp.quad(lambda u: (1 - mp.cos(w*u))*mp.exp(u/2)/mp.sinh(u), [0, 2*a])
def bound(a, N):
    mp.mp.dps = 60 + 8*N
    a = mp.mpf(a); X = mp.exp(2*a); ns = [n for n in range(2, int(X) + 1) if lam(n) > 0]
    c0 = -mp.euler - mp.pi/2 - 3*mp.log(2) - mp.log(mp.pi)
    Far = mp.log((mp.exp(a) + 1)/(mp.exp(a) - 1)) + mp.pi/2 - mp.atan(mp.sinh(a))
    Pw = lambda m: sum(lam(n)/mp.sqrt(n)*mp.cos(mp.pi*m*mp.log(n)/(4*a)) for n in ns)
    Psum = sum(lam(n)/mp.sqrt(n) for n in ns)
    if EXACT == "mixed":
        tau = Cin(mp.pi*(N + 1)/2) - err(a) - 2*Psum
    elif EXACT:
        dps0 = mp.mp.dps; tail = min(psi_exact(a, m) for m in range(N + 1, N + 80)); mp.mp.dps = dps0
        tau = tail - 2*Psum
    else:
        tau = Cin(mp.pi*(N + 1)/2) - err(a) - 2*Psum
    kap = c0 + Far + tau
    if EXACT:
        dps0 = mp.mp.dps; PS = {m: psi_exact(a, m) for m in range(1, N + 1)}; mp.mp.dps = dps0
        psil = lambda m: PS[m]
    else:
        psil = lambda m: Cin(mp.pi*m/2) + a*(1 - 2*mp.sin(mp.pi*m/2)/(mp.pi*m)) - err(a)
    s = [mp.mpf(2), (0 - 2*Pw(0) - tau)/(8*a)] + [2*(psil(m) - 2*Pw(m) - tau)/(8*a) for m in range(1, N + 1)]
    om = lambda k: mp.pi*k/(4*a)
    def gC(i, j):
        if i == 0 or j == 0:
            if i == 0 and j == 0: return a + mp.sinh(a)
            k = (j if i == 0 else i) - 1; w = om(k)
            return (mp.cos(mp.pi*k/4)*mp.sinh(a/2) + 2*w*mp.sin(mp.pi*k/4)*mp.cosh(a/2))/(w**2 + mp.mpf(1)/4)
        if i == j: return 2*a if i == 1 else a + mp.sin(mp.pi*(i - 1)/2)/(2*om(i - 1))
        wi, wj = om(i - 1), om(j - 1)
        return mp.sin(mp.pi*(i - j)/4)/(wi - wj) + mp.sin(mp.pi*(i + j - 2)/4)/(wi + wj)
    n = N + 2
    G = mp.matrix(n, n)
    for i in range(n):
        for j in range(n): G[i, j] = gC(i, j)
    L = mp.matrix(n, n)
    for j in range(n):
        d = G[j, j] - sum(L[j, k]**2 for k in range(j))
        if d <= 0: raise ValueError("G not PD at this precision")
        L[j, j] = mp.sqrt(d)
        for i in range(j + 1, n): L[i, j] = (G[i, j] - sum(L[i, k]*L[j, k] for k in range(j)))/L[j, j]
    M = L.T*mp.diag(s)*L
    return kap + min(0, min(mp.eigsy(M)[0])), kap
EXACT = (sys.argv[3] if sys.argv[3] == "mixed" else sys.argv[3] == "exact") if len(sys.argv) > 3 else False
for a in sys.argv[1].split(","):
    row = []
    for N in map(int, sys.argv[2].split(",")):
        b, k = bound(a, N); row.append(f"N={N}: {mp.nstr(b, 4)}")
    print(f"a={a}: " + " | ".join(row), flush=True)
