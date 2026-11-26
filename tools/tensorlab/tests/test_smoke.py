"""Smoke tests for the tensorlab Python module (run: python -m pytest tests/ or python tests/test_smoke.py)."""
import math
import tensorlab as tl


def test_w5_ratio_and_checks():
    num, den = tl.k23_weights()
    d = tl.k23_w5(3.0, 1.0)
    r = sum(a * b for a, b in zip(num, d)) / sum(a * b for a, b in zip(den, d))
    assert abs(r - 3 / math.sqrt(10)) < 1e-12
    rep = tl.metric_report(5, d)
    assert rep["triangle"] <= 1e-12 and rep["reshetnyak"] <= 1e-12 and rep["box"] <= 1e-12
    assert rep["l1_residual"] > 1e-3 and rep["hypermetric"] > 0


def test_fq_small():
    num, den = tl.k23_weights()
    sols = tl.min_ratio(5, num, den, ["triangle"], starts=8)
    assert abs(sols[0]["value"] - 0.75) < 1e-7


def test_box_min_toyoda():
    r3 = math.sqrt(3)
    # Toyoda Example 1.2, cycle x1 x2 x3 x4: sides 1,1,1,sqrt3, diagonals sqrt3,sqrt3
    t, s, v = tl.box_min([1, 1, 1, 3, 3, 3])
    assert v < 0
    _ = r3


def test_als_swap():
    r = tl.als(3, [(0, 1, 2), (1, 2, 2)], [(0, 2, 2)], starts=4, sweeps=300)
    assert r["residual"] < 1e-8 and r["dense_residual"] < 1e-8


def test_sqrt_rank():
    d = tl.sqrt_rank_f2(2)
    assert len(d) == 16 * 15 // 2
    assert abs(max(d) - math.sqrt(2)) < 1e-12


def test_rankplace():
    assert tl.rp_rank(0x0102) == 2 and tl.rp_rank(0x0101) == 1
    n, d, adj = tl.rp_random_regular(20, 3, 1)
    l2, lmin = tl.rp_spectrum(n, d, adj)
    bc, side, exact = tl.rp_beta_cut(n, d, adj)
    assert exact and bc <= 1 / (1 - l2) + 1e-9
    res = tl.rp_anneal(n, d, adj, 3, iters=20000, chains=2)
    rep = tl.rp_verify(n, d, adj, res[0][4], l2, lmin)
    assert rep["kernel_ok"] and abs(rep["ratio"] - res[0][1]) < 1e-9
    n, d, adj, mu, f = tl.rp_sl_cayley(2, 3, 0b1011)
    assert n == 504 and mu == 6
    assert abs(tl.rp_evaluate(n, d, adj, f)[0] - 3.738095238095238) < 1e-9


if __name__ == "__main__":
    for name, f in list(globals().items()):
        if name.startswith("test_"):
            f()
            print("ok", name)


def test_piecefloor():
    # nine-tripod one-tree optimum on Delta3 (node pod): Gamma 36, value 6 per merge
    # node (0,0): hubs R0 (index 0), C0 (3), D0 (6) on arms at radius 1
    parent = [0, 0, 0, 0]; length = [0.0, 1.0, 1.0, 1.0]
    hv = [1, 0, 0, 2, 0, 0, 3, 0, 0]
    g, sym, cs = tl.pf_one_tree("delta3", parent, length, hv)
    assert abs(g - 36) < 1e-9 and abs(sym - 6) < 1e-9
    # index-4 subgroup configuration of the limit problem: Phi = 27/8
    hv = [1, 0, 0, 0, 2, 0, 0, 0, 3, 0, 0, 0]
    assert abs(tl.pf_limit_phi("4", 3, parent, length, hv) - 27 / 8) < 1e-12
