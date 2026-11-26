//! Name-based dispatch used by the CLI binaries (and tests).

use crate::bnb::{self, Options, Problem};
use crate::cert;
use crate::problems::{clstar::{ClNear, ClStar}, hull3::Hull3, testfns::TestFn};
use std::fs::File;
use std::io::{BufReader, BufWriter, Write};

pub struct ProveReport {
    pub proved: bool,
    pub summary: String,
    pub leaves: u64,
    pub counterexamples: Vec<String>,
}

pub fn prove_generic<const N: usize, P: Problem<N>>(p: &P, opt: Options, out: Option<&str>) -> Result<ProveReport, String> {
    let o = bnb::prove(p, opt);
    let st = &o.stats;
    let mut leaves = 0;
    if let Some(path) = out {
        let f = File::create(path).map_err(|e| e.to_string())?;
        let mut w = BufWriter::new(f);
        leaves = cert::write_cert(p, &o.tree, &mut w).map_err(|e| e.to_string())?;
        w.flush().map_err(|e| e.to_string())?;
    }
    let mut ces = vec![];
    for (b, ce) in o.fails.iter().take(20) {
        match ce {
            Some((x, v)) => ces.push(format!("COUNTEREXAMPLE x = {:?} (exact floats; bits {:?}) f(x) in {:?} < {}", x,
                x.iter().map(|t| format!("{:016x}", t.to_bits())).collect::<Vec<_>>(), v, p.bound())),
            None => ces.push(format!("unclosed box {:?}", b)),
        }
    }
    let summary = format!(
        "problem {}\nstatement: {}\nresult: {}\ntime {:.2}s; leaves: natural {} meanvalue {} taylor2 {} convex {} gain {} pruned {} excluded {} FAIL {}; splits {}; max depth {}\nmin certified leaf bound {:.9} (non-convexity leaves: {:.9})",
        p.name(), p.statement(), if o.proved { "PROVED" } else { "NOT PROVED" }, o.seconds,
        st.natural, st.meanvalue, st.taylor2, st.convex, st.gain, st.pruned, st.excluded, st.fail, st.splits, st.max_depth,
        st.min_lb, st.min_lb_nonconvex
    );
    Ok(ProveReport { proved: o.proved, summary, leaves, counterexamples: ces })
}

pub fn check_generic<const N: usize, P: Problem<N>>(p: &P, path: &str) -> Result<String, String> {
    let t0 = std::time::Instant::now();
    let f = File::open(path).map_err(|e| e.to_string())?;
    let parsed = cert::parse_cert(p, BufReader::new(f))?;
    let bad = bnb::verify_leaves(p, &parsed.leaves);
    if !bad.is_empty() {
        let mut s = format!("REJECTED: {} leaves fail\n", bad.len());
        for (_, m) in bad.iter().take(10) {
            s += m;
            s += "\n";
        }
        return Err(s);
    }
    let mut counts = std::collections::BTreeMap::new();
    for (_, l) in &parsed.leaves {
        let k = match l {
            bnb::Leaf::Natural(_) => "N",
            bnb::Leaf::MeanValue(_) => "M",
            bnb::Leaf::Taylor2(_) => "T",
            bnb::Leaf::Convex { .. } => "C",
            bnb::Leaf::Pruned => "P",
            bnb::Leaf::Excluded => "X",
            bnb::Leaf::Gain { .. } => "G",
            bnb::Leaf::Fail { .. } => "F",
        };
        *counts.entry(k).or_insert(0u64) += 1;
    }
    let mut chull: Option<bnb::BoxN<N>> = None;
    for (b, l) in &parsed.leaves {
        if matches!(l, bnb::Leaf::Convex { .. } | bnb::Leaf::Gain { .. }) {
            chull = Some(match chull { None => *b, Some(h) => std::array::from_fn(|i| h[i].hull(&b[i])) });
        }
    }
    Ok(format!(
        "VERIFIED: {} >= {} on its domain\nstatement: {}\n{}{} leaves {:?}, check time {:.2}s\nhull of convexity/gain leaves: {:?}",
        p.name(), p.bound(), p.statement(),
        if counts.contains_key("X") { format!("X leaves rely on: {}\n", p.excluded_note()) } else { String::new() }, parsed.leaves.len(), counts, t0.elapsed().as_secs_f64(), chull
    ))
}

macro_rules! dispatch {
    ($name:expr, $f:ident, $($args:expr),*) => {{
        let name: &str = $name;
        if name.starts_with("hull3") {
            let p = Hull3::from_name(name)?;
            $f(&p, $($args),*)
        } else if name.starts_with("clstar") {
            let p = ClStar::from_name(name)?;
            $f(&p, $($args),*)
        } else if name.starts_with("clnear") {
            let p = ClNear::from_name(name)?;
            $f(&p, $($args),*)
        } else if name.starts_with("bowl2") || name.starts_with("valley2") || name.starts_with("ring2") {
            let p = TestFn::from_name(name)?;
            $f(&p, $($args),*)
        } else {
            Err(format!("unknown problem {name}"))
        }
    }};
}

pub fn prove_by_name(name: &str, opt: Options, out: Option<&str>) -> Result<ProveReport, String> {
    dispatch!(name, prove_generic, opt, out)
}

pub fn check_by_name(name: &str, path: &str) -> Result<String, String> {
    dispatch!(name, check_generic, path)
}

/// Read the problem name from a certificate header.
pub fn cert_problem_name(path: &str) -> Result<String, String> {
    use std::io::BufRead;
    let f = File::open(path).map_err(|e| e.to_string())?;
    for l in BufReader::new(f).lines().take(5) {
        let l = l.map_err(|e| e.to_string())?;
        if let Some(n) = l.strip_prefix("problem ") {
            return Ok(n.trim().to_string());
        }
    }
    Err("no problem line".into())
}
