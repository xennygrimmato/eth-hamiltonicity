//! Positive-definiteness certificates for interval matrices.
//!
//! `congruence_gershgorin(H, P)`: computes A = P^T H P in interval arithmetic (P an exact float matrix,
//! chosen as V diag(lambda^-1/2) from a floating-point eigendecomposition of mid(H); its choice is
//! not part of the trust base) and checks that every Gershgorin disc of A lies in (0, inf). For every
//! real symmetric H' in the interval matrix H, P^T H' P lies in A, so is PD; if P is nonsingular
//! (checked below by the same test applied to P^T P: Gershgorin PD), H' is PD by Sylvester's law of
//! inertia. The returned value is a rigorous lower bound for lambda_min(P^T H' P).
//!
//! `interval_cholesky(H)`: Cholesky in interval arithmetic; all pivots > 0 implies every symmetric
//! matrix in H is PD.

use crate::interval::I;

/// Floating-point Jacobi eigendecomposition of a symmetric matrix (heuristic, untrusted).
pub fn jacobi_eigen<const N: usize>(m: &[[f64; N]; N]) -> ([f64; N], [[f64; N]; N]) {
    let mut a = *m;
    let mut v = [[0.0; N]; N];
    for i in 0..N {
        v[i][i] = 1.0;
    }
    for _sweep in 0..100 {
        let mut off = 0.0;
        for i in 0..N {
            for j in 0..N {
                if i != j {
                    off += a[i][j] * a[i][j];
                }
            }
        }
        if off < 1e-30 {
            break;
        }
        for p in 0..N {
            for q in p + 1..N {
                if a[p][q].abs() < 1e-300 {
                    continue;
                }
                let theta = (a[q][q] - a[p][p]) / (2.0 * a[p][q]);
                let t = theta.signum() / (theta.abs() + (theta * theta + 1.0).sqrt());
                let t = if theta == 0.0 { 1.0 } else { t };
                let c = 1.0 / (t * t + 1.0).sqrt();
                let s = t * c;
                for k in 0..N {
                    let akp = a[k][p];
                    let akq = a[k][q];
                    a[k][p] = c * akp - s * akq;
                    a[k][q] = s * akp + c * akq;
                }
                for k in 0..N {
                    let apk = a[p][k];
                    let aqk = a[q][k];
                    a[p][k] = c * apk - s * aqk;
                    a[q][k] = s * apk + c * aqk;
                }
                for k in 0..N {
                    let vkp = v[k][p];
                    let vkq = v[k][q];
                    v[k][p] = c * vkp - s * vkq;
                    v[k][q] = s * vkp + c * vkq;
                }
            }
        }
    }
    let mut ev = [0.0; N];
    for i in 0..N {
        ev[i] = a[i][i];
    }
    (ev, v)
}

/// Heuristic preconditioner P = V diag(1/sqrt(lambda)) from mid(H); None if mid(H) is not PD.
pub fn choose_p<const N: usize>(h: &[[I; N]; N]) -> Option<[[f64; N]; N]> {
    let mut m = [[0.0; N]; N];
    for i in 0..N {
        for j in 0..N {
            let x = 0.5 * (h[i][j].mid() + h[j][i].mid());
            if !x.is_finite() {
                return None;
            }
            m[i][j] = x;
        }
    }
    let (ev, v) = jacobi_eigen(&m);
    let mut p = [[0.0; N]; N];
    for k in 0..N {
        if !(ev[k] > 0.0) {
            return None;
        }
        let s = 1.0 / ev[k].sqrt();
        for i in 0..N {
            p[i][k] = v[i][k] * s;
        }
    }
    Some(p)
}

/// Gershgorin lower bound for lambda_min of the symmetric interval matrix A (rigorous lower bound
/// on lambda_min of every symmetric matrix in A).
pub fn gershgorin_lb<const N: usize>(a: &[[I; N]; N]) -> f64 {
    let mut lb = f64::INFINITY;
    for k in 0..N {
        let mut r = a[k][k];
        for l in 0..N {
            if l != k {
                let m = a[k][l].abs();
                r = r - I::new(m.hi, m.hi);
            }
        }
        if !r.is_valid() {
            return f64::NEG_INFINITY;
        }
        lb = lb.min(r.lo);
    }
    lb
}

fn congruence<const N: usize>(h: &[[I; N]; N], p: &[[f64; N]; N]) -> [[I; N]; N] {
    // B = H P, A = P^T B
    let mut b = [[I::point(0.0); N]; N];
    for i in 0..N {
        for l in 0..N {
            let mut s = I::point(0.0);
            for j in 0..N {
                s = s + h[i][j] * I::point(p[j][l]);
            }
            b[i][l] = s;
        }
    }
    let mut a = [[I::point(0.0); N]; N];
    for k in 0..N {
        for l in k..N {
            let mut s = I::point(0.0);
            for i in 0..N {
                s = s + I::point(p[i][k]) * b[i][l];
            }
            a[k][l] = s;
        }
    }
    // symmetrize: the true P^T H' P is symmetric, so entry (l,k) equals entry (k,l)
    for k in 0..N {
        for l in 0..k {
            a[k][l] = a[l][k];
        }
    }
    a
}

/// Rigorous: true iff the test proves every symmetric matrix in `h` positive definite.
pub fn congruence_gershgorin<const N: usize>(h: &[[I; N]; N], p: &[[f64; N]; N]) -> bool {
    // symmetrize input by intersection (true Hessians are symmetric)
    let mut hs = *h;
    for i in 0..N {
        for j in 0..N {
            hs[i][j] = h[i][j].meet(&h[j][i]);
            if !hs[i][j].is_valid() || hs[i][j].lo > hs[i][j].hi {
                return false;
            }
        }
    }
    // P nonsingular: P^T P PD by Gershgorin
    let mut id = [[I::point(0.0); N]; N];
    for i in 0..N {
        id[i][i] = I::point(1.0);
    }
    if !(gershgorin_lb(&congruence(&id, p)) > 0.0) {
        return false;
    }
    gershgorin_lb(&congruence(&hs, p)) > 0.0
}

/// Rigorous: true iff interval Cholesky succeeds with positive pivots.
pub fn interval_cholesky<const N: usize>(h: &[[I; N]; N]) -> bool {
    let mut l = [[I::point(0.0); N]; N];
    for k in 0..N {
        let mut d = h[k][k];
        for j in 0..k {
            d = d - l[k][j].sqr();
        }
        if !d.is_valid() || !(d.lo > 0.0) {
            return false;
        }
        let lkk = d.sqrt();
        l[k][k] = lkk;
        for i in k + 1..N {
            let mut s = h[i][k].meet(&h[k][i]);
            for j in 0..k {
                s = s - l[i][j] * l[k][j];
            }
            l[i][k] = s / lkk;
        }
    }
    true
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn pd_tests() {
        // Hessian of (I) at 0: diag 4, off-diagonal 2.5 (eigenvalues 9, 1.5, 1.5); Gershgorin alone fails
        let mut h = [[I::point(2.5); 3]; 3];
        for i in 0..3 {
            h[i][i] = I::point(4.0);
        }
        assert!(!(gershgorin_lb(&h) > 0.0));
        let p = choose_p(&h).unwrap();
        assert!(congruence_gershgorin(&h, &p));
        assert!(interval_cholesky(&h));
        // indefinite: off-diagonal 4.5 gives eigenvalue 4 - 4.5 < 0
        let mut g = [[I::point(4.5); 3]; 3];
        for i in 0..3 {
            g[i][i] = I::point(4.0);
        }
        assert!(choose_p(&g).is_none() || !congruence_gershgorin(&g, &choose_p(&h).unwrap()));
        assert!(!congruence_gershgorin(&g, &p));
        assert!(!interval_cholesky(&g));
        // interval matrix containing a singular matrix must be rejected
        let mut s = h;
        s[0][1] = I::new(2.5, 4.0);
        s[1][0] = s[0][1];
        s[0][0] = I::new(4.0, 4.0);
        s[1][1] = I::new(4.0, 4.0); // contains [[4,4],[4,4]] block: singular
        assert!(!congruence_gershgorin(&s, &p));
        assert!(!interval_cholesky(&s));
    }
}
