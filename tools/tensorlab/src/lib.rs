//! tensorlab: small, fast tools for experiments on tensor prices / the asymptotic spectrum.
//!
//! Modules (usable from Rust without Python; the `python` feature adds the PyO3 module):
//! - [`metric`]: finite metrics as distance vectors, inequality families, l1 / Euclidean tests.
//! - [`opt`]: multistart augmented-Lagrangian minimisation of N.d/D.d with KKT polishing.
//! - [`models`]: CAT(0) model spaces (products of trees, Euclidean, cones over graphs).
//! - [`tensor`]: dense tensors over f64 / c64, flattening ranks, graph (EPR-network) tensors.
//! - [`restrict`]: restriction search T <= S by alternating least squares, border variant.
//! - [`ff`]: exact linear algebra over F_p (p = 2, 3) for exact restriction checks.
//! - [`k23`]: the K_{2,3} network-coding instance (parties, weights, wires).

pub mod metric;
pub mod models;
pub mod opt;
pub mod k23;
pub mod tensor;
pub mod restrict;

#[cfg(feature = "python")]
mod python;
