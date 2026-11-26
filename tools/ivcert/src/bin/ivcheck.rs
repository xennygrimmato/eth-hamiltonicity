//! Independent checker: ivcheck <certificate>  -- re-verifies every leaf, no search.
use ivcert::driver;

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.len() != 2 {
        eprintln!("usage: ivcheck <certificate>");
        std::process::exit(2);
    }
    let name = match driver::cert_problem_name(&args[1]) {
        Ok(n) => n,
        Err(e) => { eprintln!("error: {e}"); std::process::exit(2); }
    };
    match driver::check_by_name(&name, &args[1]) {
        Ok(s) => { println!("{s}"); }
        Err(e) => { println!("{e}"); std::process::exit(1); }
    }
}
