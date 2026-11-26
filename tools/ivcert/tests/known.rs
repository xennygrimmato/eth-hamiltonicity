//! End-to-end tests: known-true claims are proved and their certificates verify; false claims are
//! refused (with an exactly evaluated counterexample); tampered certificates are rejected.

use ivcert::bnb::Options;
use ivcert::driver::{check_by_name, prove_by_name};

fn tmp(name: &str) -> String {
    let d = std::env::temp_dir().join("ivcert-tests");
    std::fs::create_dir_all(&d).unwrap();
    d.join(name).to_string_lossy().to_string()
}

fn opts(depth: u32) -> Options {
    Options { max_depth: depth, ..Options::default() }
}

#[test]
fn true_claims_prove_and_check() {
    for name in ["bowl2", "valley2", "ring2:c=-1e-3", "hull3"] {
        let path = tmp(&format!("{}.cert", name.replace(':', "_")));
        let r = prove_by_name(name, opts(40), Some(&path)).unwrap();
        assert!(r.proved, "{name}: {}", r.summary);
        let c = check_by_name(name, &path);
        assert!(c.is_ok(), "{name}: {:?}", c);
    }
}

#[test]
fn hull3_without_symmetry_or_convexity_shortcuts() {
    // without symmetry pruning it still proves; without the convexity test it cannot (equality at 0)
    let mut o = opts(40);
    o.use_symmetry = false;
    assert!(prove_by_name("hull3", o, None).unwrap().proved);
    let mut o = opts(30);
    o.use_convex = false;
    o.max_fail = 50;
    let r = prove_by_name("hull3", o, None).unwrap();
    assert!(!r.proved);
}

#[test]
fn false_claims_are_refused() {
    // (name, expect an exact counterexample)
    for (name, ce) in [
        ("bowl2:c=1e-9", true),
        ("valley2:c=1e-12", true),
        ("ring2:c=1e-6", true),
        ("hull3:c=3.0001", true),
        ("hull3:k=2", true), // Hessian at 0 indefinite: F < 3 near (t,-t,0)
        ("ring2:c=0", false), // true but non-isolated minimum: must NOT be "proved", no counterexample
        ("hull3:k=8", false), // equality also at the corner (pi/2,pi/2,-pi/2): unclosed boxes there
    ] {
        let mut o = opts(30);
        o.max_fail = 20;
        let r = prove_by_name(name, o, None).unwrap();
        assert!(!r.proved, "{name} was proved?!");
        let has_ce = r.counterexamples.iter().any(|s| s.starts_with("COUNTEREXAMPLE"));
        assert_eq!(has_ce, ce, "{name}: {:?}", r.counterexamples);
    }
}

#[test]
fn tampered_certificates_are_rejected() {
    let path = tmp("hull3_tamper.cert");
    assert!(prove_by_name("hull3", opts(40), Some(&path)).unwrap().proved);
    let text = std::fs::read_to_string(&path).unwrap();
    // 1. replace the whole tree by a single natural leaf
    let i = text.find("tree\n").unwrap() + 5;
    let bad1 = format!("{}N 3\nend 1\n", &text[..i]);
    // 2. turn every Taylor leaf into a natural leaf
    let bad2 = text.replace("\nT ", "\nN ");
    // 3. claim a pruned box where the box meets the fundamental domain
    let bad3 = text.replacen("\nN ", "\nP #", 1).replace("\nP #", "\nP\n#");
    // 4. change the claimed bound
    let bad4 = text.replace("bound 4008000000000000", "bound 4008000000000001");
    // 5. swap the problem for a false variant
    let bad5 = text.replacen("problem hull3\n", "problem hull3:k=2\n", 1);
    for (k, b) in [bad1, bad2, bad3, bad4, bad5].iter().enumerate() {
        let p = tmp(&format!("bad{k}.cert"));
        std::fs::write(&p, b).unwrap();
        let name = if k == 4 { "hull3:k=2" } else { "hull3" };
        assert!(check_by_name(name, &p).is_err(), "tampering {k} not detected");
    }
}
