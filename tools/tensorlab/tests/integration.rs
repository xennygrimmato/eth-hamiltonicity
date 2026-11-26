use tensorlab::{k23, metric::*, opt::*};

#[test]
fn w5_value() {
    let m = k23::w5(3.0, 1.0);
    assert!((m.ratio(&k23::num(), &k23::den()) - 3.0 / 10f64.sqrt()).abs() < 1e-14);
    assert!(m.max_violation(&box_family_all_orders(5)).0 < 1e-12);
    assert!(m.l1_nnls().0 > 1e-3);
}

#[test]
fn fq_and_fcat5() {
    let mut c = triangle_family(5);
    c.extend(reshetnyak_family(5));
    let p = RatioProblem::new(k23::num(), k23::den(), c);
    let s = multistart(&p, &random_metric_starts(5, 24, 3), &Opts::default());
    assert!((s[0].value - 0.944605973782578821).abs() < 1e-9, "{}", s[0].value);
    let mut c = triangle_family(5);
    c.extend(box_family(5));
    let p = RatioProblem::new(k23::num(), k23::den(), c);
    let s = multistart(&p, &random_metric_starts(5, 24, 3), &Opts::default());
    assert!((s[0].value - 3.0 / 10f64.sqrt()).abs() < 1e-9, "{}", s[0].value);
}
