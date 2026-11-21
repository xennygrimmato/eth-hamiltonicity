#!/usr/bin/env python3
"""Cramer-model prediction (independent odd integers prime w.p. 2/ln N) for
E#{N in [2^k,2^(k+1)): pi([N,N+2^j)) even for all 0<=j<=k}  vs  pr_stats_31.out."""
import math,re
obs={}
for line in open("pr_stats_31.out"):
    m=re.match(r"(\d+) (\d+) (\S+) (\d+) ",line)
    if m: obs[int(m.group(1))]=int(m.group(4))
print("k  model_E[fails]  observed   (log2 N-ish growth: model ~ c*k)")
tm=to=0
for k in range(9,30):
    N=1.5*2**k; q=2/math.log(N)
    # N even (N odd is the same event shifted): [N,N+2^j) has 2^(j-1) odd numbers; new block j has 2^(j-2) odds (j>=2), j=1: one odd
    pr=1.0; prev=0
    for j in range(1,k+1):
        tot=2**(j-1); new=tot-prev; prev=tot
        pr*=(1+(1-2*q)**new)/2
    e=2**k*pr; tm+=e; to+=obs.get(k,0)
    print(k,round(e,2),obs.get(k))
print("total model",round(tm,1),"observed",to)
