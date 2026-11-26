# MET_6: 7 orbits of extreme rays found from 4000 random LP objectives (14.4s)
| orbit rep (d over pairs 01,02,..,45) | hits | cut? | orbit size | in rank cone? (c, mu, f) | best L1 error per c |
|---|---|---|---|---|---|
| [0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 1, 1] | 2386 | True | 6 | cut (diagonal placement) | [] |
| [0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 1, 1, 1, 0] | 1128 | True | 15 | cut (diagonal placement) | [] |
| [0, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 0, 0, 0] | 465 | True | 10 | cut (diagonal placement) | [] |
| [0, 1, 1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 1] | 14 | False | 60 | YES c=1 mu=2 f=['0', '0', '303', '200', '1', '203'] | [0] |
| [0, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 2] | 3 | False | 90 | YES c=1 mu=2 f=['0', '0', '1', '200', '301', '203'] | [0] |
| [1, 1, 1, 2, 2, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2] | 1 | False | 10 | YES c=1 mu=2 f=['0', '2', '303', '100', '103', '302'] | [0] |
| [1, 1, 1, 2, 2, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2] | 3 | False | 90 | not found (c <= 4, mu <= 8) | [2, 4, 1000000000, 1000000000] |
# total 17.8s

real	0m18.514s
user	0m17.641s
sys	0m0.176s
