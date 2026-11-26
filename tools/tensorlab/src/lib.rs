//! tensorlab: small, fast tools for experiments on tensor prices / the asymptotic spectrum.
//!
//! Modules (usable from Rust without Python; the `python` feature adds the PyO3 module):
//! - [`metric`]: finite metrics as distance vectors, inequality families, l1 / Euclidean tests.
//! - [`opt`]: multistart augmented-Lagrangian minimisation of N.d/D.d with KKT polishing.
//! - [`models`]: CAT(0) model spaces (products of trees, Euclidean, cones over graphs).
//! - [`tensor`]: dense tensors over f64 / c64, flattening ranks, graph (EPR-network) tensors.
//! - [`restrict`]: restriction search T <= S by ALS (R/C), Levenberg-Marquardt refinement (R), border diagnostics.
//! - exact F_2 restriction search by SAT lives in `python/f2sat.py` (python-sat).
//! - [`rankplace`]: placements into Mat_mu(F_2), rank-metric Poincaré ratios on graphs (expanders, Cayley graphs).
//! - [`piecefloor`]: the price method for pieces (b_m = (L - H_m)/delta_m), placements in Mat_mu(F_2) with sqrt(rank), Euclidean and spider-product models; exhaustive hub orbits for mu <= 3.
//! - [`k23`]: the K_{2,3} network-coding instance (parties, weights, wires).

pub mod metric;
pub mod models;
pub mod opt;
pub mod k23;
pub mod tensor;
pub mod restrict;
pub mod rankplace;
pub mod piecefloor;

#[cfg(feature = "python")]
mod python;
