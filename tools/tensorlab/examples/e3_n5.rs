//! Checks on N5 = sqrt-rank metric of {0, I, e11, e21+e22, e12+e22} in Mat_2(F_2), and W5 inside the
//! tripod x R diamond.
use tensorlab::{k23, metric::*, models::*};
fn main() {
    // Mat_2(F_2) bit index: row r at bits 2r..2r+1, entry (r,c) = bit 2r+c
    let e = |r: usize, c: usize| 1usize << (2 * r + c);
    let pts = [0usize, e(0, 0) | e(1, 1), e(0, 0), e(1, 0) | e(1, 1), e(0, 1) | e(1, 1)]; // n,s,t1,t2,t3 ~ u1,u2,v1,v2,v3
    let big = Metric::sqrt_rank_f2(2);
    let n5 = big.sub(&pts);
    let names = k23::names();
    for (k, (i, j)) in pairs(5).into_iter().enumerate() { print!("{}{}={:.6} ", names[i], names[j], n5.d[k]); }
    println!();
    let fam: Vec<Constraint> = triangle_family(5).into_iter().chain(reshetnyak_family(5)).chain(box_family(5)).collect();
    println!("N5: R={:.6} viol(tri,resh,box)={:.2e} gram_min_eig={:.4} l1 residual={:.2e} hypermetric max={:.4}",
        n5.ratio(&k23::num(), &k23::den()), n5.max_violation(&fam).0, n5.euclidean_gram_min_eig(), n5.l1_nnls().0, n5.max_hypermetric_violation(5).0);
    // tripod x R: tripod = star with centre c, legs. Encode as tree on nodes c=5, leg points.
    // diamond: n,s at spine heights +-1/sqrt2; t_i at leg distance 1/sqrt2, height 0.
    let r = 1.0 / 2f64.sqrt();
    let place = |legpos: [f64; 5], height: [f64; 5]| {
        // tree factor: points on legs 0,1,2 of a star: point k on leg leg[k] at distance legpos[k]
        let leg = [0usize, 0, 0, 1, 2];
        Metric::from_fn(5, |i, j| {
            let dt = if legpos[i] == 0.0 || legpos[j] == 0.0 || leg[i] != leg[j] { legpos[i] + legpos[j] } else { (legpos[i] - legpos[j]).abs() };
            (dt * dt + (height[i] - height[j]).powi(2)).sqrt()
        })
    };
    let n5_tl = place([0.0, 0.0, r, r, r], [r, -r, 0.0, 0.0, 0.0]);
    let diff: f64 = n5_tl.d.iter().zip(&n5.d).map(|(a, b)| (a - b).abs()).fold(0.0, f64::max);
    println!("N5 realised in tripod x R diamond: max |d - d_N5| = {:.2e}", diff);
    let l = 0.5 * r; let h = l / 3.0; // |x|+|sigma| <= 1/sqrt2 holds: l <= r, h <= r
    let w = place([0.0, 0.0, l, l, l], [h, -h, 0.0, 0.0, 0.0]);
    let w5 = k23::w5(l, h);
    let diff2: f64 = w.d.iter().zip(&w5.d).map(|(a, b)| (a - b).abs()).fold(0.0, f64::max);
    println!("W5(l={:.4},h=l/3) in diamond: max |d - d_W5| = {:.2e}, R={:.12}", l, diff2, w.ratio(&k23::num(), &k23::den()));
    // the three quadrilaterals (n, t_i, s, t_j) of N5: Euler equality (flat squares)
    for (a, b) in [(2, 3), (2, 4), (3, 4)] {
        let ex = n5.get(0, 1).powi(2) + n5.get(a, b).powi(2) - (n5.get(0, a).powi(2) + n5.get(a, 1).powi(2) + n5.get(1, b).powi(2) + n5.get(b, 0).powi(2));
        println!("  quadrilateral (n,t{},s,t{}): diag^2 - sides^2 = {:.2e}", a - 1, b - 1, ex);
    }
    let _ = binary_trees(5);
}
