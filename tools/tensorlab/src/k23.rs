//! The Okamura-Seymour K_{2,3} instance. Points: 0 = u1, 1 = u2, 2 = v1, 3 = v2, 4 = v3.
//! Supply S = six wires u_i v_j; demand T = v1v2, v2v3, v1v3, u1u2.

use crate::metric::weights;

pub const NAMES: [&str; 5] = ["u1", "u2", "v1", "v2", "v3"];
pub const N: usize = 5;

pub fn supply_wires() -> Vec<(usize, usize)> {
    vec![(0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4)]
}
pub fn demand_wires() -> Vec<(usize, usize)> {
    vec![(2, 3), (3, 4), (2, 4), (0, 1)]
}
/// Numerator weights (supply) on the 10 pairs.
pub fn num() -> Vec<f64> {
    weights(N, &supply_wires().iter().map(|&(a, b)| (a, b, 1.0)).collect::<Vec<_>>())
}
/// Denominator weights (demand) on the 10 pairs.
pub fn den() -> Vec<f64> {
    weights(N, &demand_wires().iter().map(|&(a, b)| (a, b, 1.0)).collect::<Vec<_>>())
}
pub fn names() -> Vec<String> {
    NAMES.iter().map(|s| s.to_string()).collect()
}
/// The configuration W5 in tripod x R: v_j at distance l from the spine at height 0 in three
/// half-planes, u1, u2 on the spine at heights +-h.
pub fn w5(l: f64, h: f64) -> crate::metric::Metric {
    crate::metric::Metric::from_fn(N, |i, j| {
        let u = |k: usize| k < 2;
        match (u(i), u(j)) {
            (true, true) => 2.0 * h,
            (false, false) => 2.0 * l,
            _ => (l * l + h * h).sqrt(),
        }
    })
}
