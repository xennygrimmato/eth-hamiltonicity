use std::time::Instant;
use tensorlab::rankplace::{anneal::*, graph::*};
fn main() {
    let a: Vec<String> = std::env::args().skip(1).collect();
    let n: usize = a[0].parse().unwrap();
    let iters: u64 = a[1].parse().unwrap();
    let g = random_regular(n, 4, 1);
    for pm in [[1.0, 0.0, 0.0, 0.0, 0.0, 0.0], [0.0, 1.0, 0.0, 0.0, 0.0, 0.0], [0.0, 0.0, 0.0, 1.0, 0.0, 0.0], Opts::default().p_moves] {
        let t = Instant::now();
        let r = anneal(&g, 6, Objective::Ratio, &Opts { iters, p_moves: pm, ..Default::default() }, make_init(&Init::Random { rank: 1 }, n, 6, 1));
        println!("{pm:?}: {:.2} us/move acc {} ratio {:.3}", t.elapsed().as_secs_f64() * 1e6 / iters as f64, r.accepted, r.ratio);
    }
}
