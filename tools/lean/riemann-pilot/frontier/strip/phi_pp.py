import mpmath as mp
mp.mp.dps = 30
def Phi(u):
    return sum((2*mp.pi**2*n**4*mp.e**(4.5*u) - 3*mp.pi*n**2*mp.e**(2.5*u))*mp.e**(-mp.pi*n**2*mp.e**(2*u)) for n in range(1, 8))
d2 = lambda u: mp.diff(Phi, u, 2)
I = lambda f: 2*mp.quad(f, [0, 0.5, 1, 2, 4])
PP = I(lambda u: Phi(u)**2); DD = I(lambda u: d2(u)**2); PD = I(lambda u: Phi(u)*d2(u))
perp = mp.sqrt(DD - PD**2/PP)/mp.sqrt(PP)
print("||(Phi'')_perp||/||Phi|| =", perp)
