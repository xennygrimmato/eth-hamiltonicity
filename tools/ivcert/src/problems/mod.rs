//! Problem definitions. Each problem is identified by a registry name `base[:key=value]*`;
//! the certificate stores the name and the checker rebuilds the problem from it.
pub mod clstar;
pub mod hull3;
pub mod testfns;

use std::collections::BTreeMap;

/// Parse `base:key=val:key=val`.
pub fn parse_name(name: &str) -> (String, BTreeMap<String, String>) {
    let mut it = name.split(':');
    let base = it.next().unwrap_or("").to_string();
    let mut m = BTreeMap::new();
    for kv in it {
        if let Some((k, v)) = kv.split_once('=') {
            m.insert(k.to_string(), v.to_string());
        }
    }
    (base, m)
}

pub fn param_f64(m: &BTreeMap<String, String>, k: &str, default: f64) -> Result<f64, String> {
    match m.get(k) {
        None => Ok(default),
        Some(v) => v.parse::<f64>().map_err(|e| format!("bad value for {k}: {e}")),
    }
}
