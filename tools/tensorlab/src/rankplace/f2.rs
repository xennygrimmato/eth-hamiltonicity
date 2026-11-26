//! Bit-packed square matrices over F_2 of size mu <= 8, one matrix per u64.
//!
//! Layout: row i is byte i (bits 8i..8i+7), column j is bit j of that byte. Entries outside the
//! top-left mu x mu block are zero. The difference of two matrices is their XOR.

use rand::Rng;

/// One bit in the lowest position of every byte.
pub const LSB_BYTES: u64 = 0x0101_0101_0101_0101;

/// Mask of the valid mu x mu block.
#[inline]
pub fn block_mask(mu: usize) -> u64 {
    assert!(mu >= 1 && mu <= 8);
    let row = ((1u64 << mu) - 1) & 0xFF;
    let rows = if mu == 8 { u64::MAX } else { (1u64 << (8 * mu)) - 1 };
    (row * LSB_BYTES) & rows
}

/// Rank over F_2 of a byte-row matrix (any mu <= 8). Branch-light Gaussian elimination: for each
/// nonzero row taken as pivot, its lowest set bit is cleared in all later rows at once (byte-broadcast
/// multiply). Later rows never regain a pivot bit, because everything XOR-ed into them afterwards is a
/// later row, so the nonzero pivot rows have distinct lowest bits and are independent.
#[inline(always)]
pub fn rank(mut x: u64) -> u32 {
    // fully unrolled and branch-free: a zero pivot row gives p = 0, which makes the update a no-op
    let mut r = 0u32;
    macro_rules! step {
        ($i:expr) => {{
            let p = (x >> (8 * $i)) & 0xFF;
            r += (p != 0) as u32;
            // m = 0x01 in every later row byte that contains the lowest set bit of p
            let lsb = p & p.wrapping_neg();
            let t = x & lsb.wrapping_mul(LSB_BYTES);
            let later = LSB_BYTES << (8 * ($i + 1));
            let m = (t.wrapping_add(0x7F7F_7F7F_7F7F_7F7F) >> 7) & later;
            x ^= m.wrapping_mul(p);
        }};
    }
    step!(0);
    step!(1);
    step!(2);
    step!(3);
    step!(4);
    step!(5);
    step!(6);
    r += ((x >> 56) != 0) as u32;
    r
}

/// out[w] = rank(b ^ f[w]); returns the sum. Written so that the loop vectorises (AVX-512 with
/// target-cpu=native).
#[inline]
pub fn ranks_against(b: u64, f: &[u64], out: &mut [u8]) -> i64 {
    let mut s = 0i64;
    for (o, &x) in out.iter_mut().zip(f.iter()) {
        let r = rank(b ^ x);
        *o = r as u8;
        s += r as i64;
    }
    s
}

#[inline]
pub fn rank_sum(b: u64, f: &[u64]) -> i64 {
    f.iter().map(|&x| rank(b ^ x) as i64).sum()
}

/// Reference rank (top-bit basis), used in tests.
pub fn rank_ref(x: u64) -> u32 {
    let mut basis = [0u8; 8];
    let mut r = 0;
    for i in 0..8 {
        let mut v = ((x >> (8 * i)) & 0xFF) as u8;
        while v != 0 {
            let h = 7 - v.leading_zeros() as usize;
            if basis[h] == 0 {
                basis[h] = v;
                r += 1;
                break;
            }
            v ^= basis[h];
        }
    }
    r
}

#[inline]
pub fn get(a: u64, i: usize, j: usize) -> bool {
    (a >> (8 * i + j)) & 1 == 1
}

#[inline]
pub fn row(a: u64, i: usize) -> u8 {
    ((a >> (8 * i)) & 0xFF) as u8
}

/// Matrix from rows.
pub fn from_rows(rows: &[u8]) -> u64 {
    rows.iter().enumerate().fold(0u64, |a, (i, &r)| a | ((r as u64) << (8 * i)))
}

pub fn identity(mu: usize) -> u64 {
    (0..mu).fold(0u64, |a, i| a | (1u64 << (9 * i)))
}

/// Elementary matrix e_ij.
#[inline]
pub fn unit(i: usize, j: usize) -> u64 {
    1u64 << (8 * i + j)
}

/// Rank-one matrix x y^T (x: column vector as bits 0..mu, y: row vector as bits 0..mu).
#[inline]
pub fn outer(x: u8, y: u8) -> u64 {
    // spread the bits of x into the low bit of each byte
    let mut s = 0u64;
    let mut xx = x as u64;
    let mut i = 0;
    while xx != 0 {
        if xx & 1 == 1 {
            s |= 1u64 << (8 * i);
        }
        xx >>= 1;
        i += 1;
    }
    s.wrapping_mul(y as u64)
}

/// Product A*B: row i of AB is the XOR of the rows j of B with A_ij = 1.
pub fn mul(a: u64, b: u64) -> u64 {
    let mut c = 0u64;
    for i in 0..8 {
        let mut ri = row(a, i);
        let mut acc = 0u8;
        while ri != 0 {
            let j = ri.trailing_zeros() as usize;
            acc ^= row(b, j);
            ri &= ri - 1;
        }
        c |= (acc as u64) << (8 * i);
    }
    c
}

pub fn transpose(a: u64, mu: usize) -> u64 {
    let mut t = 0u64;
    for i in 0..mu {
        for j in 0..mu {
            if get(a, i, j) {
                t |= unit(j, i);
            }
        }
    }
    t
}

/// Inverse of an invertible mu x mu matrix (None if singular).
pub fn inverse(a: u64, mu: usize) -> Option<u64> {
    let mut m: Vec<u8> = (0..mu).map(|i| row(a, i)).collect();
    let mut inv: Vec<u8> = (0..mu).map(|i| 1u8 << i).collect();
    for c in 0..mu {
        let p = (c..mu).find(|&r| (m[r] >> c) & 1 == 1)?;
        m.swap(c, p);
        inv.swap(c, p);
        for r in 0..mu {
            if r != c && (m[r] >> c) & 1 == 1 {
                m[r] ^= m[c];
                inv[r] ^= inv[c];
            }
        }
    }
    Some(from_rows(&inv))
}

/// Add row j to row i (left multiplication by I + e_ij).
#[inline]
pub fn row_op(a: u64, i: usize, j: usize) -> u64 {
    a ^ (((a >> (8 * j)) & 0xFF) << (8 * i))
}

/// Add column l to column k (right multiplication by I + e_lk).
#[inline]
pub fn col_op(a: u64, k: usize, l: usize) -> u64 {
    a ^ (((a >> l) & LSB_BYTES) << k)
}

#[inline]
pub fn random_vec<R: Rng>(rng: &mut R, mu: usize) -> u8 {
    loop {
        let v = (rng.gen::<u32>() & ((1u32 << mu) - 1)) as u8;
        if v != 0 {
            return v;
        }
    }
}

/// Uniform random rank-one matrix.
#[inline]
pub fn random_rank_one<R: Rng>(rng: &mut R, mu: usize) -> u64 {
    outer(random_vec(rng, mu), random_vec(rng, mu))
}

/// Sum of r random rank-one matrices (rank <= r).
pub fn random_rank_le<R: Rng>(rng: &mut R, mu: usize, r: usize) -> u64 {
    (0..r).fold(0u64, |a, _| a ^ random_rank_one(rng, mu))
}

#[inline]
pub fn random_matrix<R: Rng>(rng: &mut R, mu: usize) -> u64 {
    rng.gen::<u64>() & block_mask(mu)
}

/// Bits of a subspace of F_2^N (N <= 64) given by spanning vectors: rank of a list of u64 vectors.
pub fn rank_vectors(vs: &[u64]) -> u32 {
    let mut basis = [0u64; 64];
    let mut r = 0;
    for &v0 in vs {
        let mut v = v0;
        while v != 0 {
            let h = 63 - v.leading_zeros() as usize;
            if basis[h] == 0 {
                basis[h] = v;
                r += 1;
                break;
            }
            v ^= basis[h];
        }
    }
    r
}

pub fn to_string(a: u64, mu: usize) -> String {
    (0..mu)
        .map(|i| (0..mu).map(|j| if get(a, i, j) { '1' } else { '0' }).collect::<String>())
        .collect::<Vec<_>>()
        .join("/")
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::{rngs::SmallRng, SeedableRng};

    #[test]
    fn rank_matches_reference() {
        let mut rng = SmallRng::seed_from_u64(1);
        for mu in 1..=8 {
            for _ in 0..20000 {
                let a = random_matrix(&mut rng, mu);
                assert_eq!(rank(a), rank_ref(a), "{}", to_string(a, mu));
                let r1 = random_rank_le(&mut rng, mu, 2);
                assert_eq!(rank(r1), rank_ref(r1));
                assert!(rank(r1) <= 2);
            }
            assert_eq!(rank(identity(mu)), mu as u32);
            assert_eq!(rank(block_mask(mu)), 1);
        }
        // exhaustive for mu = 3
        for a in 0..512u64 {
            let m = from_rows(&[(a & 7) as u8, ((a >> 3) & 7) as u8, ((a >> 6) & 7) as u8]);
            assert_eq!(rank(m), rank_ref(m));
        }
    }

    #[test]
    fn ops() {
        let mut rng = SmallRng::seed_from_u64(2);
        for mu in 2..=8 {
            for _ in 0..500 {
                let a = random_matrix(&mut rng, mu);
                let b = random_matrix(&mut rng, mu);
                assert_eq!(mul(a, identity(mu)), a);
                assert_eq!(transpose(mul(a, b), mu), mul(transpose(b, mu), transpose(a, mu)));
                if let Some(ai) = inverse(a, mu) {
                    assert_eq!(mul(a, ai), identity(mu));
                    assert_eq!(rank(a), mu as u32);
                } else {
                    assert!(rank(a) < mu as u32);
                }
                let (i, j) = (rng.gen_range(0..mu), rng.gen_range(0..mu));
                if i != j {
                    assert_eq!(row_op(a, i, j), mul(identity(mu) ^ unit(i, j), a));
                    assert_eq!(col_op(a, i, j), mul(a, identity(mu) ^ unit(j, i)));
                }
                assert_eq!(a & !block_mask(mu), 0);
            }
        }
    }
}
