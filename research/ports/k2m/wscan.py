"""Scan weights: is the symmetric book W_{m+2} optimal up to the cut threshold?"""
import sys, numpy as np
from books import run, Rm
from multiprocessing import Pool
def cut_best(m, w):
    c = [2/(m-1)] + [m/(w + b*(m-b)) for b in range(0, m+1)]
    return min(c)
def job(arg):
    m, w = arg
    best = run(m, w, starts=150, seed=int(1000*w)+m, verbose=False)
    return m, w, best[0], Rm(m, w), cut_best(m, w), best[1]
if __name__ == "__main__":
    jobs = [(3, w) for w in (0.3, 0.7, 1.1, 1.2, 1.25, 1.3, 1.5, 2.0, 3.0)] + \
           [(4, w) for w in (2.0, 2.4, 2.5, 2.6, 3.0, 4.5, 6.0)] + \
           [(5, w) for w in (3.33, 4.17, 5.0, 5.33, 5.6, 8.0)]
    with Pool(4) as p:
        for m, w, r, rm, c, x in p.imap(job, jobs):
            tag = "W" if abs(r-rm) < 1e-8 else ("cut" if abs(r-c) < 1e-6 else "OTHER")
            print(f"m={m} w={w:5.2f} book-min={r:.9f} R_m(w)={rm:.9f} bestcut={c:.9f} -> {tag}", flush=True)
            if tag == "OTHER":
                print("    rho=", np.round(np.abs(x[:m]),4), "a=", np.round(x[m:],4), flush=True)
