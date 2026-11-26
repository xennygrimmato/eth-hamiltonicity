use ivcert::ad::{Jet2};
use ivcert::bnb::Problem;
use ivcert::interval::I;
use ivcert::problems::book::Book;
fn main() {
    let p = Book::from_name("book").unwrap();
    let w: f64 = std::env::args().nth(1).unwrap().parse().unwrap();
    let b: [I; 6] = std::array::from_fn(|i| if i < 3 { I::new(3.0 - w, 3.0 + w) } else { I::new(-w, w) });
    let x: [Jet2<6>; 6] = std::array::from_fn(|i| Jet2::var(b[i], i));
    let j = p.eval(&x);
    let h = j.hessian();
    for r in &h { println!("{:?}", r.iter().map(|e| format!("[{:.3},{:.3}]", e.lo, e.hi)).collect::<Vec<_>>()); }
    println!("choose_p: {}", ivcert::linalg::choose_p(&h).is_some());
}
