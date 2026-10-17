import mpmath as mp, json
mp.mp.dps = 40
def Phi(u, m=0):
    # derivatives via the p_m recursion
    polys = [[0, -3, 2]]
    for _ in range(m):
        c = polys[-1]; new = [mp.mpf(0)]*(len(c)+1)
        for j, cj in enumerate(c):
            if j > 0: new[j] += 2*j*cj
            new[j] += cj/2; new[j+1] += -2*cj
        polys.append(new)
    s = 0; n = 1
    while True:
        q = mp.pi*n*n*mp.e**(2*u)
        if q > 300: break
        s += sum(cj*q**j for j, cj in enumerate(polys[m]))*mp.e**(-q); n += 1
    return mp.e**(u/2)*s
rows = []
for d in ("1.0", "1.6", "2.2", "2.6"):
    J = json.load(open(f"eigs_{d}_80.json")); a = mp.mpf(d)/2
    le, lo = [mp.mpf(x["lam"]) for x in J["even"]], [mp.mpf(x["lam"]) for x in J["odd"]]
    kap = -Phi(a, 1)/Phi(a); P2 = Phi(a)**2
    T = 2*mp.pi*mp.e**(2*a); N = T/(2*mp.pi)*mp.log(T/(2*mp.pi*mp.e)) + mp.mpf(7)/8
    rows.append({"delta": d, "kappa": mp.nstr(kap, 4),
      "-ln lam_e1": mp.nstr(-mp.log(le[0]), 5), "-ln lam_o1": mp.nstr(-mp.log(lo[0]), 5), "-ln lam_e2": mp.nstr(-mp.log(le[1]), 5),
      "-ln Phi(a)^2": mp.nstr(-mp.log(P2), 5), "2pi e^{2a}": mp.nstr(2*mp.pi*mp.e**(2*a), 5),
      "Zhu 2pi^2 N/lnN": mp.nstr(2*mp.pi**2*N/mp.log(N), 5) if N > 1 else "-",
      "lam_e1/Phi(a)^2": mp.nstr(le[0]/P2, 3), "lam_o1/(kap^2 Phi^2)": mp.nstr(lo[0]/(kap**2*P2), 3)})
for r in rows: print(json.dumps(r))
