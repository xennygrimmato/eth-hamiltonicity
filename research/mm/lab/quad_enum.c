// Exact Boolean-quadratic multiplicative complexity test for <2,2,2> over F2, k <= 6,
// by enumeration (independent cross-check of the SAT result).
// Alternating forms on 8 vars = 28-bit ints. W = span of the 4 target forms.
// k decomposables D_1..D_k span a space containing W  <=>  their classes in Lambda^2/W span
// V with dim V <= k-4 and span{decomposables with class in V} contains W.
// k=6: enumerate all pairs of classes (c1,c2) (V = <c1,c2>).
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
static int pidx[8][8];
static uint32_t wedge(int l1, int l2){ uint32_t f=0; for(int u=0;u<8;u++)for(int v=u+1;v<8;v++){int a=((l1>>u)&1)&((l2>>v)&1), b=((l1>>v)&1)&((l2>>u)&1); if(a^b) f|=1u<<pidx[u][v];} return f;}
static uint32_t Wb[4]; static int Wp[4]; // echelon basis of W with pivots
static uint32_t reduceW(uint32_t f){ for(int i=0;i<4;i++) if((f>>Wp[i])&1) f^=Wb[i]; return f; }
// span test
typedef struct { uint32_t b[32]; int n; } Basis;
static void binit(Basis*B){ memset(B,0,sizeof *B); }
static int badd(Basis*B, uint32_t x){ for(int i=31;i>=0;i--) if((x>>i)&1){ if(!B->b[i]){B->b[i]=x;B->n++;return 1;} x^=B->b[i]; } return 0; }
static int bcontains(Basis*B, uint32_t x){ for(int i=31;i>=0;i--) if((x>>i)&1){ if(!B->b[i]) return 0; x^=B->b[i]; } return 1; }
static uint32_t T[4];
static int containsW(Basis*B){ for(int i=0;i<4;i++) if(!bcontains(B,T[i])) return 0; return 1; }
typedef struct { uint32_t cls, f; } Item;
static int cmp(const void*a,const void*b){ uint32_t x=((Item*)a)->cls,y=((Item*)b)->cls; return x<y?-1:x>y; }
int main(){
  int p=0; for(int u=0;u<8;u++)for(int v=u+1;v<8;v++){pidx[u][v]=p++;}
  // vars: a11 a12 a21 a22 b11 b12 b21 b22 = 0..7 ; A(i,j)=2i+j, B(j,k)=4+2j+k
  for(int i=0;i<2;i++)for(int k=0;k<2;k++){ uint32_t f=0; for(int j=0;j<2;j++){int a=2*i+j,b=4+2*j+k; f|=1u<<pidx[a][b];} T[2*i+k]=f; }
  if(getenv("TEST")){ int t=atoi(getenv("TEST"));  // positive controls
    if(t==1){T[0]=wedge(1,16);T[1]=wedge(2,32);T[2]=wedge(4,64);T[3]=wedge(8,128)^wedge(3,48);}      // needs 5
    if(t==2){T[0]=wedge(1,16)^wedge(6,96);T[1]=wedge(2,32);T[2]=wedge(4,64)^wedge(9,144);T[3]=wedge(8,128);} // needs <=6
  }
  // echelon W
  { uint32_t v[4]; memcpy(v,T,sizeof v); int r=0; for(int bit=27;bit>=0 && r<4;bit--){ int piv=-1; for(int i=r;i<4;i++) if((v[i]>>bit)&1){piv=i;break;} if(piv<0) continue; uint32_t t=v[r];v[r]=v[piv];v[piv]=t; for(int i=0;i<4;i++) if(i!=r && ((v[i]>>bit)&1)) v[i]^=v[r]; Wb[r]=v[r]; Wp[r]=bit; r++; } if(r!=4){printf("W rank %d\n",r);return 1;} }
  uint8_t *seen=calloc(1u<<28,1); Item *it=malloc(sizeof(Item)*70000); int N=0;
  for(int l1=1;l1<256;l1++)for(int l2=1;l2<256;l2++){ uint32_t f=wedge(l1,l2); if(!f||seen[f]) continue; seen[f]=1; it[N].f=f; it[N].cls=reduceW(f); N++; }
  qsort(it,N,sizeof(Item),cmp);
  // class table
  int *cs=malloc(sizeof(int)*(N+1)); uint32_t *cv=malloc(sizeof(uint32_t)*N); int C=0;
  for(int i=0;i<N;i++){ if(i==0||it[i].cls!=it[i-1].cls){ cs[C]=i; cv[C]=it[i].cls; C++; } } cs[C]=N;
  printf("decomposable forms %d, classes %d\n",N,C);
  // lookup class value -> index via binary search
  #define FIND(x) ({ int lo=0,hi=C-1,res=-1; while(lo<=hi){int m=(lo+hi)/2; if(cv[m]==(x)){res=m;break;} if(cv[m]<(x)) lo=m+1; else hi=m-1;} res; })
  int c0 = FIND(0u);
  Basis B; binit(&B); if(c0>=0) for(int i=cs[c0];i<cs[c0+1];i++) badd(&B,it[i].f);
  printf("k<=4 feasible: %d (class-0 forms span dim %d)\n", c0>=0 && containsW(&B), B.n);
  Basis B0=B; long found5=0;
  for(int c=0;c<C;c++){ if(c==c0) continue; Basis B1=B0; for(int i=cs[c];i<cs[c+1];i++) badd(&B1,it[i].f); if(containsW(&B1)) found5++; }
  printf("k<=5 feasible classes: %ld\n",found5);
  long found6=0, pairs=0;
  for(int c1=0;c1<C;c1++){ if(c1==c0) continue; Basis B1=B0; for(int i=cs[c1];i<cs[c1+1];i++) badd(&B1,it[i].f);
    for(int c2=c1+1;c2<C;c2++){ if(c2==c0) continue; pairs++; Basis B2=B1; for(int i=cs[c2];i<cs[c2+1];i++) badd(&B2,it[i].f);
      int c3=FIND(cv[c1]^cv[c2]); if(c3>=0) for(int i=cs[c3];i<cs[c3+1];i++) badd(&B2,it[i].f);
      if(containsW(&B2)){ found6++; if(found6<=3) printf("k=6 witness classes %x %x\n",cv[c1],cv[c2]); } } }
  printf("pairs checked %ld, k<=6 feasible: %ld\n",pairs,found6);
  return 0;
}
