//! Dense tensors over f64 / Complex64 with labelled-axis contraction (a tiny einsum), flattening
//! ranks, local maps, and graph-state (EPR network) tensors built from wire lists.

use nalgebra::{ComplexField, DMatrix};
use num_complex::Complex64;

/// Scalar types usable in tensors (f64 and Complex64).
pub trait Scalar: ComplexField<RealField = f64> + Copy + Send + Sync + 'static {
    fn from_f64(x: f64) -> Self;
    fn conj_(self) -> Self;
    fn abs2(self) -> f64;
}
impl Scalar for f64 {
    fn from_f64(x: f64) -> Self { x }
    fn conj_(self) -> Self { self }
    fn abs2(self) -> f64 { self * self }
}
impl Scalar for Complex64 {
    fn from_f64(x: f64) -> Self { Complex64::new(x, 0.0) }
    fn conj_(self) -> Self { self.conj() }
    fn abs2(self) -> f64 { self.norm_sqr() }
}

/// Dense row-major tensor with one label per axis.
#[derive(Clone, Debug)]
pub struct Tensor<T: Scalar> {
    pub shape: Vec<usize>,
    pub labels: Vec<usize>,
    pub data: Vec<T>,
}

pub fn strides(shape: &[usize]) -> Vec<usize> {
    let mut s = vec![1; shape.len()];
    for i in (0..shape.len().saturating_sub(1)).rev() {
        s[i] = s[i + 1] * shape[i + 1];
    }
    s
}

impl<T: Scalar> Tensor<T> {
    pub fn zeros(shape: Vec<usize>, labels: Vec<usize>) -> Self {
        let n = shape.iter().product();
        Tensor { shape, labels, data: vec![T::zero(); n] }
    }
    pub fn from_vec(shape: Vec<usize>, labels: Vec<usize>, data: Vec<T>) -> Self {
        assert_eq!(shape.iter().product::<usize>(), data.len());
        assert_eq!(shape.len(), labels.len());
        Tensor { shape, labels, data }
    }
    pub fn len(&self) -> usize { self.data.len() }
    pub fn is_empty(&self) -> bool { self.data.is_empty() }
    pub fn norm2(&self) -> f64 { self.data.iter().map(|x| x.abs2()).sum() }
    pub fn axis(&self, label: usize) -> usize {
        self.labels.iter().position(|&l| l == label).expect("label not found")
    }
    /// Permute axes to the given label order.
    pub fn permute_to(&self, order: &[usize]) -> Tensor<T> {
        let perm: Vec<usize> = order.iter().map(|&l| self.axis(l)).collect();
        if perm.iter().enumerate().all(|(i, &p)| i == p) {
            return self.clone();
        }
        let new_shape: Vec<usize> = perm.iter().map(|&p| self.shape[p]).collect();
        let old_str = strides(&self.shape);
        let src_str: Vec<usize> = perm.iter().map(|&p| old_str[p]).collect();
        let n = self.data.len();
        let mut out = Vec::with_capacity(n);
        let r = new_shape.len();
        let mut idx = vec![0usize; r];
        let mut off = 0usize;
        for _ in 0..n {
            out.push(self.data[off]);
            // increment
            let mut a = r;
            while a > 0 {
                a -= 1;
                idx[a] += 1;
                off += src_str[a];
                if idx[a] < new_shape[a] {
                    break;
                }
                off -= src_str[a] * idx[a];
                idx[a] = 0;
            }
        }
        Tensor { shape: new_shape, labels: order.to_vec(), data: out }
    }
    /// Matricise: rows = given labels (in order), columns = the rest (in current order).
    pub fn matricize(&self, rows: &[usize]) -> (DMatrix<T>, Vec<usize>) {
        let cols: Vec<usize> = self.labels.iter().cloned().filter(|l| !rows.contains(l)).collect();
        let mut order = rows.to_vec();
        order.extend(&cols);
        let p = self.permute_to(&order);
        let nr: usize = rows.iter().map(|&l| self.shape[self.axis(l)]).product();
        let nc = p.data.len() / nr.max(1);
        // row-major data -> DMatrix (column-major): build transposed then transpose
        let m = DMatrix::from_row_slice(nr, nc, &p.data);
        (m, cols)
    }
    /// Numerical rank of the flattening rows|rest (relative tolerance on singular values).
    pub fn flattening_rank(&self, rows: &[usize], rtol: f64) -> usize {
        let (m, _) = self.matricize(rows);
        let sv = m.singular_values();
        let mx = sv.iter().cloned().fold(0.0, f64::max);
        sv.iter().filter(|&&s| s > rtol * mx).count()
    }
    /// Contract with another tensor over all shared labels.
    pub fn contract(&self, other: &Tensor<T>) -> Tensor<T> {
        let shared: Vec<usize> = self.labels.iter().cloned().filter(|l| other.labels.contains(l)).collect();
        let a_free: Vec<usize> = self.labels.iter().cloned().filter(|l| !shared.contains(l)).collect();
        let b_free: Vec<usize> = other.labels.iter().cloned().filter(|l| !shared.contains(l)).collect();
        let mut ao = a_free.clone();
        ao.extend(&shared);
        let mut bo = shared.clone();
        bo.extend(&b_free);
        let ap = self.permute_to(&ao);
        let bp = other.permute_to(&bo);
        let k: usize = shared.iter().map(|&l| self.shape[self.axis(l)]).product();
        let m = ap.data.len() / k.max(1);
        let n = bp.data.len() / k.max(1);
        let am = DMatrix::from_row_slice(m, k, &ap.data);
        let bm = DMatrix::from_row_slice(k, n, &bp.data);
        let c = am * bm;
        let mut shape: Vec<usize> = a_free.iter().map(|&l| self.shape[self.axis(l)]).collect();
        shape.extend(b_free.iter().map(|&l| other.shape[other.axis(l)]));
        let mut labels = a_free;
        labels.extend(b_free);
        // c column-major -> row-major
        let ct = c.transpose();
        Tensor { shape, labels, data: ct.as_slice().to_vec() }
    }
    /// Apply a matrix M (new_dim x old_dim) to axis `label`, keeping the label.
    pub fn apply(&self, label: usize, m: &DMatrix<T>) -> Tensor<T> {
        let tmp = usize::MAX - 7;
        let mt = Tensor::from_vec(vec![m.nrows(), m.ncols()], vec![tmp, label], m.transpose().as_slice().to_vec());
        let mut r = mt.contract(self);
        let ax = r.axis(tmp);
        r.labels[ax] = label;
        // restore the original axis position
        r.permute_to(&self.labels)
    }
    pub fn scale(&mut self, c: T) {
        for x in self.data.iter_mut() {
            *x *= c;
        }
    }
    pub fn sub_norm2(&self, other: &Tensor<T>) -> f64 {
        let o = other.permute_to(&self.labels);
        self.data.iter().zip(&o.data).map(|(a, b)| (*a - *b).abs2()).sum()
    }
}

/// A wire network: `nparties` parties; wire w = (p, q, dim) gives an EPR pair sum_i e_i (x) e_i.
#[derive(Clone, Debug)]
pub struct Network {
    pub nparties: usize,
    pub wires: Vec<(usize, usize, usize)>,
}

impl Network {
    pub fn new(nparties: usize, wires: Vec<(usize, usize, usize)>) -> Self {
        for &(p, q, d) in &wires {
            assert!(p != q && p < nparties && q < nparties && d >= 1);
        }
        Network { nparties, wires }
    }
    /// Legs at party p: list of (wire index, dim), in wire order.
    pub fn legs(&self, p: usize) -> Vec<(usize, usize)> {
        self.wires
            .iter()
            .enumerate()
            .filter(|(_, w)| w.0 == p || w.1 == p)
            .map(|(k, w)| (k, w.2))
            .collect()
    }
    /// Local dimension at p (product of its leg dims).
    pub fn local_dim(&self, p: usize) -> usize {
        self.legs(p).iter().map(|l| l.1).product()
    }
    /// log2 of the flattening rank across (mask | complement) = sum of log2 dims of crossing wires.
    pub fn cut_log_rank(&self, mask: u64) -> f64 {
        self.wires
            .iter()
            .filter(|w| ((mask >> w.0) & 1) != ((mask >> w.1) & 1))
            .map(|w| (w.2 as f64).log2())
            .sum()
    }
    /// Dense tensor with one axis per party (label = party index), local index = mixed radix over
    /// the party's legs in wire order (first leg most significant).
    pub fn dense<T: Scalar>(&self) -> Tensor<T> {
        let dims: Vec<usize> = (0..self.nparties).map(|p| self.local_dim(p)).collect();
        let mut t = Tensor::zeros(dims.clone(), (0..self.nparties).collect());
        let str_ = strides(&dims);
        // enumerate wire index assignments
        let nw = self.wires.len();
        let mut ix = vec![0usize; nw];
        let total: usize = self.wires.iter().map(|w| w.2).product();
        let legs: Vec<Vec<(usize, usize)>> = (0..self.nparties).map(|p| self.legs(p)).collect();
        for _ in 0..total {
            let mut off = 0;
            for p in 0..self.nparties {
                let mut loc = 0;
                for &(w, d) in &legs[p] {
                    loc = loc * d + ix[w];
                }
                off += loc * str_[p];
            }
            t.data[off] = T::one();
            for k in (0..nw).rev() {
                ix[k] += 1;
                if ix[k] < self.wires[k].2 {
                    break;
                }
                ix[k] = 0;
            }
        }
        t
    }
    /// The network as a list of per-party "node" tensors for contraction with maps: party p gets a
    /// delta-free description: returns for each party the list of bond labels (wire index).
    pub fn bond_labels(&self, p: usize) -> Vec<usize> {
        self.legs(p).iter().map(|l| l.0).collect()
    }
}

/// Random matrix with entries N(0,1) (real) or complex Gaussian.
pub fn random_matrix<T: Scalar, R: rand::Rng>(r: usize, c: usize, rng: &mut R, complex: bool) -> DMatrix<T> {
    use rand_distr_like::normal;
    DMatrix::from_fn(r, c, |_, _| {
        let re = normal(rng);
        if complex {
            // T is Complex64 here; build via from_f64 + i*im using ComplexField ops
            let im = normal(rng);
            T::from_f64(re) + T::from_f64(im) * imag_unit::<T>()
        } else {
            T::from_f64(re)
        }
    })
}

fn imag_unit<T: Scalar>() -> T {
    // sqrt(-1) in T: for f64 this is NaN-free 0 (never used for real), for Complex64 it is i.
    let m1 = T::from_f64(-1.0);
    let s = m1.sqrt();
    if s.clone().abs2().is_nan() { T::zero() } else { s }
}

pub mod rand_distr_like {
    /// Box-Muller standard normal.
    pub fn normal<R: rand::Rng>(rng: &mut R) -> f64 {
        let u1: f64 = rng.gen::<f64>().max(1e-300);
        let u2: f64 = rng.gen();
        (-2.0 * u1.ln()).sqrt() * (2.0 * std::f64::consts::PI * u2).cos()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn epr_ranks() {
        // triangle of wires dims 2,3,4
        let net = Network::new(3, vec![(0, 1, 2), (1, 2, 3), (0, 2, 4)]);
        let t: Tensor<f64> = net.dense();
        assert_eq!(t.shape, vec![8, 6, 12]);
        assert_eq!(t.flattening_rank(&[0], 1e-10), 8);
        assert_eq!(t.flattening_rank(&[1], 1e-10), 6);
        assert!((t.norm2() - 24.0).abs() < 1e-12);
    }
    #[test]
    fn contract_matches_apply() {
        let net = Network::new(2, vec![(0, 1, 3)]);
        let t: Tensor<f64> = net.dense();
        let m = DMatrix::from_fn(2, 3, |i, j| (i * 3 + j) as f64);
        let a = t.apply(0, &m);
        assert_eq!(a.shape, vec![2, 3]);
        // EPR with map on first leg = the matrix itself
        for i in 0..2 {
            for j in 0..3 {
                assert_eq!(a.data[i * 3 + j], m[(i, j)]);
            }
        }
    }
    #[test]
    fn complex_unit() {
        let i: Complex64 = imag_unit();
        assert!((i - Complex64::new(0.0, 1.0)).norm() < 1e-15);
    }
}
