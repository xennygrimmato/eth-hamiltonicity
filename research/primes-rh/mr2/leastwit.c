// Least strong-pseudoprime witness w(n) for all odd composite n in [9, N].
// gcc -O3 -march=native -fopenmp leastwit.c -o leastwit -lm ; ./leastwit 10000000000
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <omp.h>
typedef uint64_t u64; typedef unsigned __int128 u128;
static inline u64 mont_inv(u64 n){u64 x=n; for(int i=0;i<5;i++) x*=2-n*x; return x;} // n*x=1 mod 2^64
static inline u64 mmul(u64 a,u64 b,u64 n,u64 ninv){u128 t=(u128)a*b; u64 m=(u64)t*ninv; u64 r=(t>>64)-(((u128)m*n)>>64); return (int64_t)r<0? r+n : r;} // result in [0,n) when using signed trick
// strong probable prime test base a (a < n not required). returns 1 if n passes (a is a liar or a%n==0)
static int sprp(u64 n,u64 a,u64 ninv,u64 one,u64 r2,u64 d,int s){
    a%=n; if(a==0) return 0; // a | n : witness (n composite)
    u64 x=mmul(a,r2,n,ninv); // montgomery form
    u64 y=one; u64 e=d;
    // left-to-right
    int top=63-__builtin_clzll(e);
    y=x;
    for(int i=top-1;i>=0;i--){ y=mmul(y,y,n,ninv); if((e>>i)&1) y=mmul(y,x,n,ninv);}
    u64 mone=n-one;
    if(y==one||y==mone) return 1;
    for(int i=1;i<s;i++){ y=mmul(y,y,n,ninv); if(y==mone) return 1; if(y==one) return 0;}
    return 0;
}
#define MAXW 64
int main(int argc,char**argv){
    u64 N=argc>1? strtoull(argv[1],0,10):1000000000ULL;
    u64 sq=(u64)sqrtl((long double)N)+2;
    // base primes
    char*bs=calloc(sq+1,1); u64 np=0; u64*bp=malloc(sizeof(u64)*(sq/2+10));
    for(u64 i=3;i<=sq;i+=2){ if(!bs[i]){bp[np++]=i; for(u64 j=i*i;j<=sq;j+=2*i) bs[j]=1;}}
    static const int sp[]={2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,103,107,109,113};
    const u64 SEG=1ULL<<22; // odds per segment
    u64 nseg=(N/2)/SEG+1;
    // global records
    u64 first[MAXW]; for(int i=0;i<MAXW;i++) first[i]=0; // first n with w(n)=sp[i]
    u64 cnt[MAXW]; memset(cnt,0,sizeof cnt);
    // per decade best ratio
    double best[25]; u64 bestn[25]; int bestw[25]; for(int i=0;i<25;i++){best[i]=0;bestn[i]=0;bestw[i]=0;}
    #pragma omp parallel
    {
        unsigned char*sv=malloc(SEG);
        u64 lfirst[MAXW]; for(int i=0;i<MAXW;i++) lfirst[i]=~0ULL; u64 lcnt[MAXW]; memset(lcnt,0,sizeof lcnt);
        double lbest[25]; u64 lbestn[25]; int lbestw[25]; for(int i=0;i<25;i++){lbest[i]=0;lbestn[i]=0;lbestw[i]=0;}
        #pragma omp for schedule(dynamic,4)
        for(u64 sgi=0;sgi<nseg;sgi++){
            u64 lo=2*sgi*SEG+1; // odd numbers lo+2k
            memset(sv,0,SEG);
            u64 hi=lo+2*SEG;
            for(u64 pi=0;pi<np;pi++){ u64 p=bp[pi]; if(p*p>=hi) break; u64 st=p*p; if(st<lo){ st=((lo+p-1)/p)*p; if(!(st&1)) st+=p;} for(u64 j=(st-lo)/2;j<SEG;j+=p) sv[j]=1;}
            for(u64 k=0;k<SEG;k++){
                if(!sv[k]) continue; u64 n=lo+2*k; if(n>N) break; if(n<9) continue;
                u64 ninv=mont_inv(n);
                u64 one=(-n)%n; // 2^64 mod n
                u64 d=n-1; int s=__builtin_ctzll(d); d>>=s;
                // base 2 fast: need montgomery of 2 = 2*one mod n
                u64 two=one+one; if(two>=n) two-=n;
                u64 y=two; int top=63-__builtin_clzll(d);
                for(int i=top-1;i>=0;i--){ y=mmul(y,y,n,ninv); if((d>>i)&1){ y+=y; if(y>=n) y-=n; } }
                u64 mone=n-one; int pass=0;
                if(y==one||y==mone) pass=1; else for(int i=1;i<s;i++){ y=mmul(y,y,n,ninv); if(y==mone){pass=1;break;} if(y==one) break; }
                int wi=0;
                if(pass){
                    u64 r2=(u64)(((u128)one*one)%n);
                    for(wi=1;wi<30;wi++){ if(!sprp(n,sp[wi],ninv,one,r2,d,s)) break; }
                }
                lcnt[wi]++; if(n<lfirst[wi]) lfirst[wi]=n;
                double ln=log((double)n); double ratio=sp[wi]/(ln*ln); int dec=(int)floor(log10((double)n)+1e-12);
                if(ratio>lbest[dec]){lbest[dec]=ratio;lbestn[dec]=n;lbestw[dec]=sp[wi];}
            }
        }
        #pragma omp critical
        { for(int i=0;i<MAXW;i++){ cnt[i]+=lcnt[i]; if(lfirst[i]!=~0ULL && (first[i]==0||lfirst[i]<first[i])) first[i]=lfirst[i]; }
          for(int i=0;i<25;i++) if(lbest[i]>best[i]||(lbest[i]==best[i]&&lbestn[i]<bestn[i]&&lbestn[i])){best[i]=lbest[i];bestn[i]=lbestn[i];bestw[i]=lbestw[i];} }
        free(sv);
    }
    printf("N=%llu\n",(unsigned long long)N);
    printf("w  count  first_n  w/ln^2(first_n)\n");
    for(int i=0;i<30;i++) if(cnt[i]){ double ln=log((double)first[i]); printf("%d %llu %llu %.6f\n",sp[i],(unsigned long long)cnt[i],(unsigned long long)first[i],sp[i]/(ln*ln)); }
    printf("decade  max ratio w/ln^2 n   n   w\n");
    for(int i=0;i<25;i++) if(bestn[i]) printf("1e%d %.6f %llu %d\n",i,best[i],(unsigned long long)bestn[i],bestw[i]);
    return 0;
}
