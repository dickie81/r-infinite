/* Gauss periods at the split primes of Z[w] (order 6) or Z[i] (order 4).
   For each split prime p <= PMAX, take the primary prime pi = a + b*root above p
   (Z[w]: a = 1 mod 3, b = 0 mod 3;  Z[i]: (a,b) = (1,0) or (3,2) mod 4),
   r = image of the root (w or i) in Z/p with a + b r = 0 mod p, a generator g of (Z/p)^*,
   j0 with g^{(p-1)/N} = zeta^{j0} mod p (zeta = 1+r for N = 6, zeta = r for N = 4),
   c with e(Tr(x/(pi*delta))) = e(c x/p) for rational x, and the N periods
   S_j = sum_{t = j mod N} e(c g^t / p),  t = 0..p-2.
   Then g(chi^a) = sum_j zeta_N^{a j0 j} S_j for the order-N character chi = (./pi)_N.
   Output: p a b r j0 c Re(S_0) Im(S_0) ... per line. */
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <stdint.h>

typedef long long ll;
static ll pw(ll b, ll e, ll m){ ll r=1%m; b%=m; if(b<0)b+=m; while(e){ if(e&1) r=(__int128)r*b%m; b=(__int128)b*b%m; e>>=1;} return r; }
static int isprime(ll n){ if(n<2) return 0; for(ll d=2; d*d<=n; d++) if(n%d==0) return 0; return 1; }
static ll md(ll x, ll m){ x%=m; return x<0? x+m : x; }

int main(int argc, char **argv){
  char field = argv[1][0];           /* 'w' or 'i' */
  ll PMAX = atoll(argv[2]);
  int N = (field=='w') ? 6 : 4;
  for(ll p=5; p<=PMAX; p++){
    if(!isprime(p)) continue;
    if(field=='w' && p%3!=1) continue;
    if(field=='i' && p%4!=1) continue;
    /* find primary (a,b) of norm p */
    ll PA[2],PB[2]; int found=0;
    ll R=(ll)sqrt((double)4*p)+2;
    for(ll b=-R; b<=R && found<2; b++) for(ll a=-R; a<=R && found<2; a++){
      ll nn = (field=='w') ? a*a-a*b+b*b : a*a+b*b;
      if(nn!=p) continue;
      /* run over units */
      ll ua[6],ub[6]; int nu;
      if(field=='w'){ /* 1, w, w^2, -1, -w, -w^2 ; (a+bw)*w = -b + (a-b)w */
        ll x=a,y=b; nu=6;
        for(int k=0;k<3;k++){ ua[k]=x; ub[k]=y; ua[k+3]=-x; ub[k+3]=-y; ll nx=-y, ny=x-y; x=nx; y=ny; }
      } else { ll x=a,y=b; nu=4; for(int k=0;k<4;k++){ ua[k]=x; ub[k]=y; ll nx=-y, ny=x; x=nx; y=ny; } }
      for(int k=0;k<nu;k++){
        ll x=ua[k], y=ub[k]; int prim;
        if(field=='w') prim = (md(x,3)==1 && md(y,3)==0);
        else prim = ((md(x,4)==1 && md(y,4)==0) || (md(x,4)==3 && md(y,4)==2));
        if(prim){ int dup=0; for(int u=0;u<found;u++) if(PA[u]==x && PB[u]==y) dup=1;
                  if(!dup){ PA[found]=x; PB[found]=y; found++; } break; }
      }
    }
    if(found!=2){ fprintf(stderr,"primaries for %lld: %d\n",p,found); return 1; }
    for(int which=0; which<2; which++){ ll A=PA[which], B=PB[which];
    ll r = md(-A * pw(md(B,p), p-2, p), p);
    /* generator */
    ll q=p-1, fac[64]; int nf=0; ll t=q;
    for(ll d=2; d*d<=t; d++) if(t%d==0){ fac[nf++]=d; while(t%d==0) t/=d; }
    if(t>1) fac[nf++]=t;
    ll g=2; for(;;g++){ int ok=1; for(int k=0;k<nf;k++) if(pw(g,q/fac[k],p)==1){ok=0;break;} if(ok) break; }
    ll zeta = (field=='w') ? md(1+r,p) : r;
    ll gN = pw(g, q/N, p); int j0=-1; ll cur=1;
    for(int j=0;j<N;j++){ if(cur==gN){ j0=j; break;} cur=(__int128)cur*zeta%p; }
    if(j0<0){ fprintf(stderr,"no j0 for %lld\n",p); return 1; }
    /* additive character: Z[w]: Tr(x/(pi sqrt(-3))) = -b x/p ; Z[i]: Tr(x/(2 pi)) = a x/p */
    ll c = (field=='w') ? md(-B,p) : md(A,p);
    double Sr[6]={0},Si[6]={0};
    ll x=1; double w0 = 2.0*M_PI/(double)p;
    for(ll tt=0; tt<q; tt++){
      ll m = (__int128)c*x % p;
      double ang = w0*(double)m;
      int j = tt % N;
      Sr[j]+=cos(ang); Si[j]+=sin(ang);
      x = (__int128)x*g % p;
    }
    printf("%lld %lld %lld %lld %d %lld", p, A, B, r, j0, c);
    for(int j=0;j<N;j++) printf(" %.12g %.12g", Sr[j], Si[j]);
    printf("\n");
    }
  }
  return 0;
}
