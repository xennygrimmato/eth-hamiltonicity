//! Print all leaf-test bounds for one box of a problem (debugging aid).
//! cargo run --release --example debug_box -- book "lo,hi;lo,hi;..."
use ivcert::bnb::{self, Problem};
use ivcert::interval::I;
use ivcert::problems::book::Book;
fn main() {
    let a: Vec<String> = std::env::args().collect();
    let p = Book::from_name(&a[1]).unwrap();
    let v: Vec<I> = a[2].split(';').map(|s| { let w: Vec<f64> = s.split(',').map(|x| x.trim().parse().unwrap()).collect(); I::new(w[0], w[1]) }).collect();
    let b: [I; 6] = std::array::from_fn(|i| v[i]);
    println!("natural {:e}", bnb::lb_natural(&p, &b));
    println!("meanvalue {:e}", bnb::lb_meanvalue(&p, &b));
    println!("taylor2 {:e}", bnb::lb_taylor2(&p, &b));
    println!("f(center) {:?}", bnb::eval_point(&p, &bnb::center(&b)));
    let _ = p.bound();
}
