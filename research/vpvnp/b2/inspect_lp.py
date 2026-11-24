import itertools, numpy as np
from metric_lp import *
S=['R','C','D']; delta={'R':1,'C':1,'D':1}
# re-solve and dump
pts = [('leg', i) for i in range(18)] + [('hub', k, g) for k in S for g in range(3)]
import metric_lp
val,out,L = solve(S,delta)
print(val,out,L)
