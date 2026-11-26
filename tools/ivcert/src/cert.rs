//! Certificate format (text, deterministic):
//!
//! ```text
//! ivcert-certificate v1
//! problem <registry name>
//! dim <N>
//! bound <hex64>            # f64 bits of the claimed lower bound c
//! domain <hex lo> <hex hi>  (N lines)
//! tree
//! <preorder lines>
//! end <number of leaves>
//! ```
//! Preorder lines: `S d` (bisect coordinate d at the float midpoint lo + 0.5 (hi - lo)),
//! `N lb`, `M lb`, `T lb` (lb informative only), `P` (pruned by symmetry),
//! `C lb x*_0..x*_{N-1} [P_00 .. P_{N-1,N-1} | chol]` (x* and P as f64 bit patterns in hex),
//! `G lb x* m P..` (gain test, P the m = |C|^2 preconditioner entries), `X` (excluded: covered by a
//! lemma or another certificate, see the problem's note),
//! `F` (unclosed box; a certificate containing F is rejected).
//! The checker rebuilds every box from the tree, so coverage of the domain is structural.

use crate::bnb::{split, BoxN, Leaf, Node, Problem};
use std::io::{BufRead, Write};

fn hx(x: f64) -> String {
    format!("{:016x}", x.to_bits())
}
fn unhx(s: &str) -> Result<f64, String> {
    u64::from_str_radix(s, 16).map(f64::from_bits).map_err(|e| format!("bad hex {s}: {e}"))
}

pub fn write_cert<const N: usize, P: Problem<N>, W: Write>(p: &P, tree: &Node<N>, w: &mut W) -> std::io::Result<u64> {
    writeln!(w, "ivcert-certificate v1")?;
    writeln!(w, "problem {}", p.name())?;
    writeln!(w, "# {}", p.statement().replace('\n', " "))?;
    writeln!(w, "dim {}", N)?;
    writeln!(w, "bound {} # {}", hx(p.bound()), p.bound())?;
    for b in p.domain().iter() {
        writeln!(w, "domain {} {} # [{}, {}]", hx(b.lo), hx(b.hi), b.lo, b.hi)?;
    }
    writeln!(w, "tree")?;
    let mut leaves = 0u64;
    fn go<const N: usize, W: Write>(n: &Node<N>, w: &mut W, leaves: &mut u64) -> std::io::Result<()> {
        match n {
            Node::Split(d, a, b) => {
                writeln!(w, "S {d}")?;
                go(a, w, leaves)?;
                go(b, w, leaves)?;
            }
            Node::Leaf(l) => {
                *leaves += 1;
                match l {
                    Leaf::Natural(x) => writeln!(w, "N {:.6e}", x)?,
                    Leaf::MeanValue(x) => writeln!(w, "M {:.6e}", x)?,
                    Leaf::Taylor2(x) => writeln!(w, "T {:.6e}", x)?,
                    Leaf::Pruned => writeln!(w, "P")?,
                    Leaf::Excluded => writeln!(w, "X")?,
                    Leaf::Gain { lb, xs, pm } => {
                        write!(w, "G {:.17e}", lb)?;
                        for x in xs {
                            write!(w, " {}", hx(*x))?;
                        }
                        write!(w, " {}", pm.len())?;
                        for x in pm {
                            write!(w, " {}", hx(*x))?;
                        }
                        writeln!(w)?;
                    }
                    Leaf::Fail { .. } => writeln!(w, "F")?,
                    Leaf::Convex { lb, xs, pm } => {
                        write!(w, "C {:.17e}", lb)?;
                        for x in xs {
                            write!(w, " {}", hx(*x))?;
                        }
                        match pm {
                            Some(m) => {
                                for r in m {
                                    for x in r {
                                        write!(w, " {}", hx(*x))?;
                                    }
                                }
                            }
                            None => write!(w, " chol")?,
                        }
                        writeln!(w)?;
                    }
                }
            }
        }
        Ok(())
    }
    go(tree, w, &mut leaves)?;
    writeln!(w, "end {leaves}")?;
    Ok(leaves)
}

pub struct Parsed<const N: usize> {
    pub problem: String,
    pub leaves: Vec<(BoxN<N>, Leaf<N>)>,
}

fn strip(s: &str) -> &str {
    match s.find('#') {
        Some(i) => s[..i].trim(),
        None => s.trim(),
    }
}

/// Parse a certificate and rebuild the leaf boxes; checks header against the problem definition.
pub fn parse_cert<const N: usize, P: Problem<N>, R: BufRead>(p: &P, r: R) -> Result<Parsed<N>, String> {
    let mut lines = r.lines().map(|l| l.map_err(|e| e.to_string()));
    let mut next = || -> Result<String, String> {
        loop {
            let l = lines.next().ok_or("unexpected end of file")??;
            let s = strip(&l).to_string();
            if !s.is_empty() {
                return Ok(s);
            }
        }
    };
    if next()? != "ivcert-certificate v1" {
        return Err("bad magic".into());
    }
    let pl = next()?;
    let name = pl.strip_prefix("problem ").ok_or("expected problem")?.to_string();
    if name != p.name() {
        return Err(format!("problem mismatch: {name} vs {}", p.name()));
    }
    let dl = next()?;
    if dl != format!("dim {N}") {
        return Err("dim mismatch".into());
    }
    let bl = next()?;
    let bv = unhx(bl.strip_prefix("bound ").ok_or("expected bound")?)?;
    if bv.to_bits() != p.bound().to_bits() {
        return Err("bound mismatch with problem definition".into());
    }
    let dom = p.domain();
    for i in 0..N {
        let l = next()?;
        let f: Vec<&str> = l.split_whitespace().collect();
        if f.len() != 3 || f[0] != "domain" {
            return Err("bad domain line".into());
        }
        let (lo, hi) = (unhx(f[1])?, unhx(f[2])?);
        if lo.to_bits() != dom[i].lo.to_bits() || hi.to_bits() != dom[i].hi.to_bits() {
            return Err("domain mismatch with problem definition".into());
        }
    }
    if next()? != "tree" {
        return Err("expected tree".into());
    }
    // iterative preorder rebuild
    let mut leaves = vec![];
    let mut stack: Vec<BoxN<N>> = vec![dom];
    while let Some(b) = stack.pop() {
        let l = next()?;
        let f: Vec<&str> = l.split_whitespace().collect();
        match f[0] {
            "S" => {
                let d: usize = f.get(1).ok_or("S needs dim")?.parse().map_err(|_| "bad dim")?;
                if d >= N {
                    return Err("split dim out of range".into());
                }
                let (lb, rb) = split(&b, d).ok_or("degenerate split")?;
                stack.push(rb);
                stack.push(lb);
            }
            "N" | "M" | "T" => {
                let x: f64 = f.get(1).ok_or("missing lb")?.parse().map_err(|_| "bad lb")?;
                let leaf = match f[0] {
                    "N" => Leaf::Natural(x),
                    "M" => Leaf::MeanValue(x),
                    _ => Leaf::Taylor2(x),
                };
                leaves.push((b, leaf));
            }
            "P" => leaves.push((b, Leaf::Pruned)),
            "X" => leaves.push((b, Leaf::Excluded)),
            "G" => {
                let lb: f64 = f.get(1).ok_or("missing lb")?.parse().map_err(|_| "bad lb")?;
                if f.len() < 3 + N {
                    return Err("short G line".into());
                }
                let mut xs = [0.0; N];
                for i in 0..N {
                    xs[i] = unhx(f[2 + i])?;
                }
                let m: usize = f[2 + N].parse().map_err(|_| "bad G count")?;
                if f.len() != 3 + N + m {
                    return Err("bad G line".into());
                }
                let pm: Result<Vec<f64>, String> = (0..m).map(|i| unhx(f[3 + N + i])).collect();
                leaves.push((b, Leaf::Gain { lb, xs, pm: pm? }));
            }
            "F" => leaves.push((b, Leaf::Fail { counterexample: None })),
            "C" => {
                let lb: f64 = f.get(1).ok_or("missing lb")?.parse().map_err(|_| "bad lb")?;
                if f.len() < 2 + N {
                    return Err("short C line".into());
                }
                let mut xs = [0.0; N];
                for i in 0..N {
                    xs[i] = unhx(f[2 + i])?;
                }
                let pm = if f.len() == 3 + N && f[2 + N] == "chol" {
                    None
                } else if f.len() == 2 + N + N * N {
                    let mut m = [[0.0; N]; N];
                    for i in 0..N {
                        for j in 0..N {
                            m[i][j] = unhx(f[2 + N + i * N + j])?;
                        }
                    }
                    Some(m)
                } else {
                    return Err("bad C line".into());
                };
                leaves.push((b, Leaf::Convex { lb, xs, pm }));
            }
            other => return Err(format!("unknown node {other}")),
        }
    }
    let e = next()?;
    let n: usize = e.strip_prefix("end ").ok_or("expected end")?.parse().map_err(|_| "bad end")?;
    if n != leaves.len() {
        return Err("leaf count mismatch".into());
    }
    Ok(Parsed { problem: name, leaves })
}

