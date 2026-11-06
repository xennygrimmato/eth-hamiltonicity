#!/bin/sh
# follow-up runs: random-start general search, dense-only rows, exhaustive single-slot neighbourhoods
cd "$(dirname "$0")"
{
for f in s1_L3_n16_Q8_rho1_r4_s3 s1_G4_n16_Q8_rho1_r4_s1 s1_L3_n24_Q8_rho1_r4_s1 s1_L3_n16_Q10_rho1_r4_s2; do
  echo "python3 stage2_general.py designs/$f.pkl 4000 2 mixedrand >> stage2_rand.out"
done
for f in s1_L3_n16_Q4_rho1_r4_s1 s1_L3_n16_Q8_rho1_r4_s3 s1_G3_n16_Q8_rho1_r4_s1 s1_L3_n16_Q8_rho2_r4_s1; do
  echo "python3 stage2_general.py designs/$f.pkl 150 3 dense >> stage2_dense.out"
done
for f in s1_L3_n16_Q8_rho1_r4_s3 s1_L3_n16_Q10_rho1_r4_s2 s1_G4_n16_Q8_rho1_r4_s1 s1_G4_n16_Q10_rho1_r4_s1; do
  echo "python3 neighbourhood.py designs/$f.pkl >> neighbourhood.out"
done
for f in s1_L3_n20_Q8_rho1_r4_s1 s1_L3_n24_Q8_rho1_r4_s1; do
  echo "python3 neighbourhood.py designs/$f.pkl 3 >> neighbourhood.out"
done
} > batch3.cmds
cat batch3.cmds | xargs -P 3 -I CMD sh -c "CMD"
