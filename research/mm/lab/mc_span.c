// Exact unrestricted XOR-AND multiplicative complexity for small quadratic maps (n <= 8 inputs),
// by search over the span S_j = span{1, x_1..x_n, G_1..G_j} of available functions (truth tables).
//
// A circuit with k ANDs computes the targets T  <=>  there is a chain S_0 < S_1 < ... < S_k with
// S_{j+1} = S_j + <u*v>, u,v in S_j, and T subset of S_k.  The state is only the subspace S_j.
// Let rem(S) = dim(T + S) - dim(S).  Each gate lowers rem by at most 1, so prune rem(S_j) > k-j.
// A gate is a REDUCER if u*v lies in S+T (then S' = S + <t> for a class t of T mod S: at most
// 2^rem - 1 possible successors, whatever u,v are) and a HELPER otherwise (only allowed while
// rem(S_j) <= k-j-1).  For fixed u, v -> u*v is F2-linear, so "which classes t are reachable"
// is a rank test per u.  Visited states are memoised by a 128-bit hash of the RREF of S.
// Gate 1 ranges over orbit representatives of planes (passed on stdin as pairs l1 l2) or over all
// planes if none given.
//
// usage: mc_span <problem> <k> [orbitfile]      problem: mm222 | pm3 | v123 | pm2 | f4
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

typedef struct { uint64_t w[4]; } V;
static int NIN, NROWS;
static V ONE;
static inline V vx(V a, V b){ V r; for(int i=0;i<4;i++) r.w[i]=a.w[i]^b.w[i]; return r; }
static inline V va(V a, V b){ V r; for(int i=0;i<4;i++) r.w[i]=a.w[i]&b.w[i]; return r; }
static inline int vz(V a){ return !(a.w[0]|a.w[1]|a.w[2]|a.w[3]); }
static inline int vtop(V a){ for(int i=3;i>=0;i--) if(a.w[i]) return 64*i+63-__builtin_clzll(a.w[i]); return -1; }
static inline int vbit(V a,int b){ return (a.w[b>>6]>>(b&63))&1; }

typedef struct { V b[64]; int piv[64]; int n; } Ech;   // echelon basis, distinct pivots
static V reduce(const Ech*E, V x){ for(int i=0;i<E->n;i++) if(vbit(x,E->piv[i])) x=vx(x,E->b[i]); return x; }
// keep echelon sorted by decreasing pivot so a single pass reduces fully
static int ech_add(Ech*E, V x){ x=reduce(E,x); if(vz(x)) return 0; int p=vtop(x);
  // eliminate pivot p from the others (RREF) to keep canonical
  for(int i=0;i<E->n;i++) if(vbit(E->b[i],p)) E->b[i]=vx(E->b[i],x);
  int pos=E->n; while(pos>0 && E->piv[pos-1]<p){ E->b[pos]=E->b[pos-1]; E->piv[pos]=E->piv[pos-1]; pos--; }
  E->b[pos]=x; E->piv[pos]=p; E->n++; return 1; }

static V X[8]; static V T[16]; static int NT; static int K;
// memo
#define HBITS 26
static uint64_t *H1,*H2; static long nstates=0, nfound=0;
static int memo(const Ech*S){ uint64_t a=1469598103934665603ULL, b=0x9e3779b97f4a7c15ULL;
  for(int i=0;i<S->n;i++) for(int j=0;j<4;j++){ a=(a^S->b[i].w[j])*1099511628211ULL; b=(b+S->b[i].w[j])*0xff51afd7ed558ccdULL; b^=b>>33; }
  if(!a) a=1; uint64_t m=(1ULL<<HBITS)-1, h=a&m;
  while(H1[h]){ if(H1[h]==a && H2[h]==b) return 1; h=(h+1)&m; }
  H1[h]=a; H2[h]=b; nstates++; return 0; }

static int rem_of(const Ech*S){ Ech E=*S; int r=0; for(int i=0;i<NT;i++) r+=ech_add(&E,T[i]); return r; }

static int verbose_depth=1;
static int dfs(Ech*S, V*G, int ng, int j){
  int rem=rem_of(S);
  if(rem==0){ nfound++; return 1; }
  if(j==K || rem>K-j) return 0;
  if(memo(S)) return 0;
  int helpers_ok = (rem <= K-j-1);
  // reduced target classes basis
  Ech ST=*S; V tb[16]; int nt=0; for(int i=0;i<NT;i++){ V r=reduce(&ST,T[i]); if(!vz(r)){ tb[nt++]=r; ech_add(&ST,T[i]); } }
  // tb are representatives (reduced mod S progressively); class space mod S spanned by reduce(S, tb)
  V tcls[16]; for(int i=0;i<nt;i++) tcls[i]=reduce(S,tb[i]);
  int ncls=1<<nt; char reach[1<<16]; memset(reach,0,ncls);
  V u; memset(&u,0,sizeof u);
  for(long gc=1; gc < (1L<<ng); gc++){
    int bit=__builtin_ctzl(gc); u=vx(u,G[bit]);
    Ech R; R.n=0; V rr[64]; int nr=0;
    for(int i=0;i<ng;i++){ V p=reduce(S,va(u,G[i])); if(!vz(p)){ if(ech_add(&R,p)) rr[nr++]=p; } }
    if(R.n==0) continue;
    for(int c=1;c<ncls;c++){ if(reach[c]) continue; V t; memset(&t,0,sizeof t); for(int i=0;i<nt;i++) if((c>>i)&1) t=vx(t,tcls[i]);
      t=reduce(S,t); if(vz(reduce(&R,t))) reach[c]=1; }
    if(helpers_ok){
      // every nonzero element of span(rr) not in (T+S)/S gives a helper successor
      for(long m=1;m<(1L<<nr);m++){ V w; memset(&w,0,sizeof w); for(int i=0;i<nr;i++) if((m>>i)&1) w=vx(w,rr[i]);
        if(vz(reduce(&ST,w))) continue;  // lies in S+T: reducer, handled below
        Ech S2=*S; ech_add(&S2,w); G[ng]=w;
        if(dfs(&S2,G,ng+1,j+1)) return 1; }
    }
  }
  for(int c=1;c<ncls;c++) if(reach[c]){ V t; memset(&t,0,sizeof t); for(int i=0;i<nt;i++) if((c>>i)&1) t=vx(t,tcls[i]);
    Ech S2=*S; ech_add(&S2,t); G[ng]=t; if(dfs(&S2,G,ng+1,j+1)) return 1; }
  return 0;
}

static void setup(const char*p){
  if(!strcmp(p,"mm222")||!strcmp(p,"v123")) NIN=8; else if(!strcmp(p,"pm3")) NIN=6; else NIN=4;
  NROWS=1<<NIN; memset(&ONE,0,sizeof ONE);
  for(int r=0;r<NROWS;r++) ONE.w[r>>6]|=1ULL<<(r&63);
  for(int i=0;i<NIN;i++){ memset(&X[i],0,sizeof(V)); for(int r=0;r<NROWS;r++) if((r>>i)&1) X[i].w[r>>6]|=1ULL<<(r&63); }
  NT=0;
  #define P(a,b) va(X[a],X[b])
  if(!strcmp(p,"mm222")){ // a11 a12 a21 a22 = 0..3 (A(i,j)=2i+j), b = 4+2j+k
    for(int i=0;i<2;i++)for(int k=0;k<2;k++){ V t; memset(&t,0,sizeof t); for(int j=0;j<2;j++) t=vx(t,P(2*i+j,4+2*j+k)); T[NT++]=t; } }
  else if(!strcmp(p,"v123")){ // <1,2,3>: x0,x1 ; B 2x3 = 2..7, B(j,k)=2+3j+k
    for(int k=0;k<3;k++){ V t; memset(&t,0,sizeof t); for(int j=0;j<2;j++) t=vx(t,P(j,2+3*j+k)); T[NT++]=t; } }
  else if(!strcmp(p,"pm3")){ for(int d=0;d<5;d++){ V t; memset(&t,0,sizeof t); for(int u=0;u<3;u++){int v=d-u; if(v>=0&&v<3) t=vx(t,P(u,3+v));} T[NT++]=t; } }
  else if(!strcmp(p,"pm2")){ T[NT++]=P(0,2); T[NT++]=vx(P(0,3),P(1,2)); T[NT++]=P(1,3); }
  else if(!strcmp(p,"f4")){ T[NT++]=vx(P(0,2),P(1,3)); T[NT++]=vx(vx(P(0,3),P(1,2)),P(1,3)); }
}

int main(int argc,char**argv){
  setup(argv[1]); K=atoi(argv[2]);
  H1=calloc(1ULL<<HBITS,8); H2=calloc(1ULL<<HBITS,8);
  Ech S0; S0.n=0; ech_add(&S0,ONE); for(int i=0;i<NIN;i++) ech_add(&S0,X[i]);
  V G[64]; for(int i=0;i<NIN;i++) G[i]=X[i];
  int ok=0;
  if(argc>3){ // first gate from orbit file: lines "l1 l2"
    FILE*f=fopen(argv[3],"r"); int l1,l2, no=0;
    while(fscanf(f,"%d %d",&l1,&l2)==2){ V u,v; memset(&u,0,sizeof u); memset(&v,0,sizeof v);
      for(int i=0;i<NIN;i++){ if((l1>>i)&1) u=vx(u,X[i]); if((l2>>i)&1) v=vx(v,X[i]); }
      V g=va(u,v); Ech S1=S0; if(!ech_add(&S1,g)) continue; G[NIN]=g; no++;
      int r=dfs(&S1,G,NIN+1,1);
      fprintf(stderr,"orbit %d (%d,%d): %s  states so far %ld\n",no,l1,l2,r?"FOUND":"none",nstates);
      if(r){ ok=1; break; } }
  } else ok=dfs(&S0,G,NIN,0);
  printf("%s k=%d: %s (states %ld)\n",argv[1],K,ok?"CIRCUIT EXISTS":"NO CIRCUIT",nstates);
  return 0;
}
