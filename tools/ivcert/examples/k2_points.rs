//! Evaluate a k2far/k2near problem at points read from stdin (one point per line, 6 floats), printing
//! the enclosure of f and whether the point box is excluded (debugging / cross-check aid).
//! cargo run --release --example k2_points -- "k2far:lam=9/10:eta=6/5:case=c:s=+++" < pts.txt
use ivcert::bnb::{self, Problem};
use ivcert::interval::I;
use ivcert::problems::k2m::K2;
use std::io::BufRead;
fn main() {
    let a: Vec<String> = std::env::args().collect();
    let p = K2::from_name(&a[1]).unwrap();
    for l in std::io::stdin().lock().lines() {
        let v: Vec<f64> = l.unwrap().split_whitespace().map(|x| x.parse().unwrap()).collect();
        let x: [f64; 6] = std::array::from_fn(|i| v[i]);
        let b: [I; 6] = std::array::from_fn(|i| I::point(x[i]));
        let f = bnb::eval_point(&p, &x);
        println!("{:.17e} {:.17e} {}", f.lo, f.hi, p.excluded(&b) as u8);
    }
}
