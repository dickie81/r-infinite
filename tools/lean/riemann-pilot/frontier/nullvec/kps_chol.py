import math, sys, kprimeside as ps
from flint import arb, ctx
def build(xv, K, drop=()):
    a=arb(repr(xv)).log()/2; w=[arb(k)*arb.pi()/a for k in range(K)]; s=[1 if k%2==0 else -1 for k in range(K)]
    Sv,Sd,Pv,Pd=ps.phi_parts(a,w,K,xv,[(p,n) for p,n in ps.prime_powers(xv) if p not in drop])
    val,dd=list(Sv),list(Sd)
    for p in Pv:
        for k in range(K): val[k]+=Pv[p][k]; dd[k]+=Pd[p][k]
    M=ps.assemble(K,w,val,dd,s); Pk=[s[k]*(a/2).sinh()/(w[k]*w[k]+arb(1)/4) for k in range(K)]
    return [[M[j,k]+Pk[j]*Pk[k] for k in range(K)] for j in range(K)]
def chol_pivots(A):
    n=len(A); L=[[arb(0)]*n for _ in range(n)]; piv=[]
    for j in range(n):
        d=A[j][j]-sum((L[j][k]*L[j][k] for k in range(j)), arb(0)); piv.append(d)
        if not d > 0: return j, piv
        L[j][j]=d.sqrt()
        for i in range(j+1,n): L[i][j]=(A[i][j]-sum((L[i][k]*L[j][k] for k in range(j)), arb(0)))/L[j][j]
    return None, piv
if __name__=="__main__":
    for xv in map(float, sys.argv[2:]):
        K=max(40,int(15*xv)+40)
        with ctx.workprec(int(sys.argv[1])):
            bad,piv=chol_pivots(build(xv,K))
            lp=[float(p.mid().abs_lower().log()/math.log(10)) if p!=0 else -999 for p in piv]
            print(xv,K,"first non-positive pivot:",bad, "pivot there:", piv[bad].str(5) if bad is not None else "-", "| min log10 pivot so far", round(min(lp),1))
