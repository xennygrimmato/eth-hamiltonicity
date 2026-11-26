//! rankplace: placements f: V(G) -> Mat_mu(F_2) (mu <= 8, bit-packed) and the ratio
//! E_pairs D_f / E_edges D_f, D_f(u,v) = rank(f(u) - f(v)), against cut metrics and spectral bounds.
//! See research/ports/middle/notes.md §4, §5, §9.
//!
//! - [`f2`]: bit-packed F_2 matrices, rank, products, inverses, random low-rank matrices.
//! - [`graph`]: regular graphs, random d-regular, cycles, tori, named cubic graphs.
//! - [`groups`]: GF(2^k), Cayley graphs of SL_m(F_{2^k}) (elementary or random generators), LPS X^{p,q}
//!   (PGL_2 / PSL_2 over F_q), structured placements g -> gW and g -> M_g P M_g^{-1}.
//! - [`spectral`]: lambda_2, lambda_min by dense eigensolver (n <= 2000) or Lanczos.
//! - [`cut`]: beta_cut exactly (n <= 24/30) or by sweeps + annealing (lower bound).
//! - [`anneal`]: parallel simulated annealing with incremental updates; objectives ratio / Lagrangian /
//!   pairs-under-edge-bound.
//! - [`verify`]: kernel inequality (Proposition S), consequences (a)-(c), spectral bound (e), JSON output.

pub mod anneal;
pub mod cut;
pub mod f2;
pub mod graph;
pub mod groups;
pub mod spectral;
pub mod verify;
