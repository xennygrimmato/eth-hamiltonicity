//! Scan wire instances on 5 parties (u1,u2,v1,v2,v3): each of the 10 pairs is unused, supply x m or
//! demand x m (m <= MAXM). For a metric d (W5 or N5) report instances with the largest gap between the
//! cut bound and the d bound f_d = sum_S d / sum_T d, together with the routing (flow) value
//! f_flow = min over the 25 extreme rays of the metric cone MET_5 (15 cuts + 10 K_{2,3} metrics).
//! Usage: e3_scan <w5|n5> <maxm> <top>
use tensorlab::{k23, metric::*};
use rayon::prelude::*;

fn k23_rays() -> Vec<Metric> {
    // path metric of K_{2,3} for each choice of the 2-side {a,b}: d=1 across, 2 within a side
    let mut v = vec![];
    for a in 0..5 { for b in a + 1..5 {
        v.push(Metric::from_fn(5, |i, j| { let s = |k: usize| k == a || k == b; if s(i) == s(j) { 2.0 } else { 1.0 } }));
    } }
    v
}

fn main() {
    let a: Vec<String> = std::env::args().collect();
    let which = a[1].clone();
    let maxm: usize = a[2].parse().unwrap();
    let top: usize = a[3].parse().unwrap();
    let d = if which == "w5" { k23::w5(3.0, 1.0) } else {
        Metric::from_fn(5, |i, j| if (i < 2) == (j < 2) { 2f64.sqrt() } else { 1.0 })
    };
    let cuts: Vec<Metric> = (1..16u64).map(|m| Metric::cut(5, m)).collect();
    let mut rays = cuts.clone(); rays.extend(k23_rays());
    let opts = 2 * maxm + 1; // 0, s1..smaxm, d1..dmaxm
    let total = opts.pow(10);
    let names = k23::names();
    let pr = pairs(5);
    let mut res: Vec<(f64, f64, f64, f64, usize)> = (0..total).into_par_iter().filter_map(|code| {
        let mut c = code; let mut s = [0f64; 10]; let mut t = [0f64; 10];
        for k in 0..10 { let o = c % opts; c /= opts; if o >= 1 && o <= maxm { s[k] = o as f64 } else if o > maxm { t[k] = (o - maxm) as f64 } }
        if t.iter().sum::<f64>() == 0.0 { return None; }
        let r = |m: &Metric| { let num: f64 = m.d.iter().zip(&s).map(|(x, y)| x * y).sum(); let den: f64 = m.d.iter().zip(&t).map(|(x, y)| x * y).sum(); if den > 0.0 { num / den } else { f64::INFINITY } };
        let fcut = cuts.iter().map(|m| r(m)).fold(f64::INFINITY, f64::min);
        let fflow = rays.iter().map(|m| r(m)).fold(f64::INFINITY, f64::min);
        if fflow == 0.0 || !fcut.is_finite() { return None; }
        let fd = r(&d);
        if fd >= fcut - 1e-12 { return None; }
        Some((fcut / fd, fcut, fd, fflow, code))
    }).collect();
    res.sort_by(|x, y| y.0.partial_cmp(&x.0).unwrap().then((x.4).cmp(&y.4)));
    println!("metric {} maxm {}: {} instances with f_d < f_cut", which, maxm, res.len());
    let mut seen: Vec<(i64, i64, i64)> = vec![];
    let mut shown = 0;
    for (g, fc, fd, ff, code) in &res {
        let key = ((g * 1e9) as i64, (fc * 1e9) as i64, (ff * 1e9) as i64);
        if seen.contains(&key) { continue; } seen.push(key);
        let mut c = *code; let mut sup = vec![]; let mut dem = vec![];
        for k in 0..10 { let o = c % opts; c /= opts; let (i, j) = pr[k];
            if o >= 1 && o <= maxm { sup.push(format!("{}{}x{}", names[i], names[j], o)) } else if o > maxm { dem.push(format!("{}{}x{}", names[i], names[j], o - maxm)) } }
        println!("gap f_cut/f_d={:.5}  f_cut={:.5} f_d={:.5} f_flow={:.5} | supply {} | demand {}", g, fc, fd, ff, sup.join(" "), dem.join(" "));
        shown += 1; if shown >= top { break; }
    }
}
