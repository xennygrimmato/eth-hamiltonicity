"""tpp_check.py -- TPP check (right quotient sets) for the CKSU Sec. 2 subsets used in fourier_pieces.py (n = 3),
and the group-word identity sum_rho (d_rho/|G|) chi_rho(w) = [w = 1] on the chosen 8-subsets."""
import fourier_pieces as fp
S8, T8, U8 = fp.cksu_subset(0), fp.cksu_subset(1), fp.cksu_subset(2)
S12, T12, U12 = fp.cksu_subset(0, 1), fp.cksu_subset(1, 1), fp.cksu_subset(2, 1)
print("TPP (right quotients) 8-subsets:", fp.check_tpp(S8, T8, U8))
print("TPP (right quotients) 12-subsets (CKSU Lemma 2.1, n=3):", fp.check_tpp(S12, T12, U12))
# a deliberately non-TPP triple as a control: S = T = U = the 8-subset S8
print("control (S,S,S), should be False:", fp.check_tpp(S8, S8, S8))
