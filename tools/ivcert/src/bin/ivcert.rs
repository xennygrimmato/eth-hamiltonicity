//! Prover CLI:  ivcert <problem-name> [--out cert.txt] [--max-depth D] [--no-mv] [--no-taylor2] [--no-convex]
use ivcert::bnb::Options;
use ivcert::driver;

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.len() < 2 {
        eprintln!("usage: ivcert <problem-name> [--out FILE] [--max-depth D] [--no-mv] [--no-taylor2] [--no-convex] [--threads T]");
        std::process::exit(2);
    }
    let name = &args[1];
    let mut opt = Options::default();
    let mut out: Option<String> = None;
    let mut i = 2;
    while i < args.len() {
        match args[i].as_str() {
            "--out" => { out = Some(args[i + 1].clone()); i += 1; }
            "--max-depth" => { opt.max_depth = args[i + 1].parse().unwrap(); i += 1; }
            "--threads" => {
                let t: usize = args[i + 1].parse().unwrap();
                rayon::ThreadPoolBuilder::new().num_threads(t).build_global().unwrap();
                i += 1;
            }
            "--max-fail" => { opt.max_fail = args[i + 1].parse().unwrap(); i += 1; }
            "--no-mv" => opt.use_mv = false,
            "--no-taylor2" => opt.use_taylor2 = false,
            "--no-convex" => opt.use_convex = false,
            "--no-symmetry" => opt.use_symmetry = false,
            a => { eprintln!("unknown arg {a}"); std::process::exit(2); }
        }
        i += 1;
    }
    match driver::prove_by_name(name, opt, out.as_deref()) {
        Ok(r) => {
            println!("{}", r.summary);
            if let Some(o) = &out { println!("certificate: {} ({} leaves)", o, r.leaves); }
            for c in &r.counterexamples { println!("{c}"); }
            std::process::exit(if r.proved { 0 } else { 1 });
        }
        Err(e) => { eprintln!("error: {e}"); std::process::exit(2); }
    }
}
