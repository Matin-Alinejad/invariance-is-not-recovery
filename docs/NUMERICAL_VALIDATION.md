# Numerical validation

**Verdict: PASS (121/121 checks).**

All reported numerical quantities checked here are recomputed directly from the supplied experiment CSVs; no value is hand-transcribed into the validation layer.

| Check | Recomputed | Expected | Verdict |
|---|---:|---:|:---:|
| primary 10-seed groups exceeding 0.05 | 6 | 6 | PASS |
| primary 10-seed max F1 half-width | 0.06952779131 | 0.0695277913 | PASS |
| primary 20-seed groups exceeding 0.05 | 0 | 0 | PASS |
| primary 20-seed max F1 half-width | 0.04051276347 | 0.0405127635 | PASS |
| theorem-aligned RR/SW topology-size combinations | 9 | 9 | PASS |
| theorem-aligned mean quadratic-complete precision_mean | 0.01874587772 | 0.0187458777 | PASS |
| theorem-aligned mean quadratic-complete recall_mean | -0.0007962962963 | -0.0007962963 | PASS |
| theorem-aligned mean quadratic-complete f1_mean | 0.009142862642 | 0.0091428626 | PASS |
| theorem-aligned mean quadratic-complete exact_recovery_mean | 0.5111111111 | 0.5111111111 | PASS |
| theorem-aligned quadratic effective fraction | 0.4456943063 | 0.4456943063 | PASS |
| random_regular_d2 p100 complete precision_mean | 0.9809773482 | 0.980977 | PASS |
| random_regular_d2 p100 complete recall_mean | 0.999 | 0.999 | PASS |
| random_regular_d2 p100 complete f1_mean | 0.9898770669 | 0.989877 | PASS |
| random_regular_d2 p100 complete exact_recovery_mean | 0.2 | 0.2 | PASS |
| random_regular_d2 p100 quad precision_mean | 0.999009901 | 0.99901 | PASS |
| random_regular_d2 p100 quad recall_mean | 0.999 | 0.999 | PASS |
| random_regular_d2 p100 quad f1_mean | 0.998999975 | 0.999 | PASS |
| random_regular_d2 p100 quad exact_recovery_mean | 0.8 | 0.8 | PASS |
| small_world_k2 p100 complete precision_mean | 0.9739412115 | 0.973941 | PASS |
| small_world_k2 p100 complete recall_mean | 1 | 1 | PASS |
| small_world_k2 p100 complete f1_mean | 0.9867400469 | 0.98674 | PASS |
| small_world_k2 p100 complete exact_recovery_mean | 0.05 | 0.05 | PASS |
| small_world_k2 p100 quad precision_mean | 0.9995049505 | 0.999505 | PASS |
| small_world_k2 p100 quad recall_mean | 1 | 1 | PASS |
| small_world_k2 p100 quad f1_mean | 0.9997512438 | 0.999751 | PASS |
| small_world_k2 p100 quad exact_recovery_mean | 0.95 | 0.95 | PASS |
| retention rate 0.1 mean F1 | 0.993081314 | 0.993081 | PASS |
| retention rate 0.1 mean effective fraction | 0.787861554 | 0.787862 | PASS |
| retention rate 0.3 mean F1 | 0.9991305661 | 0.999131 | PASS |
| retention rate 0.3 mean effective fraction | 0.4504134677 | 0.450413 | PASS |
| retention rate 0.5 mean F1 | 0.9979834329 | 0.997983 | PASS |
| retention rate 0.5 mean effective fraction | 0.2186026009 | 0.218603 | PASS |
| retention 0.3_minus_0.1 mean F1 delta | 0.006049252157 | 0.006049 | PASS |
| retention 0.3_minus_0.1 positive intervals | 4 | 4 | PASS |
| retention 0.3_minus_0.1 negative intervals | 0 | 0 | PASS |
| retention 0.3_minus_0.1 overlap intervals | 0 | 0 | PASS |
| retention 0.5_minus_0.1 mean F1 delta | 0.004902118898 | 0.004902 | PASS |
| retention 0.5_minus_0.1 positive intervals | 2 | 2 | PASS |
| retention 0.5_minus_0.1 negative intervals | 0 | 0 | PASS |
| retention 0.5_minus_0.1 overlap intervals | 2 | 2 | PASS |
| retention 0.5_minus_0.3 mean F1 delta | -0.001147133259 | -0.001147 | PASS |
| retention 0.5_minus_0.3 positive intervals | 0 | 0 | PASS |
| retention 0.5_minus_0.3 negative intervals | 0 | 0 | PASS |
| retention 0.5_minus_0.3 overlap intervals | 4 | 4 | PASS |
| alpha f1 mean delta | -0.01523489024 | -0.01523489 | PASS |
| alpha f1 positive intervals | 0 | 0 | PASS |
| alpha f1 negative intervals | 15 | 15 | PASS |
| alpha f1 overlap intervals | 21 | 21 | PASS |
| alpha precision mean delta | -0.0275743571 | -0.02757436 | PASS |
| alpha precision positive intervals | 0 | 0 | PASS |
| alpha precision negative intervals | 16 | 16 | PASS |
| alpha precision overlap intervals | 20 | 20 | PASS |
| alpha recall mean delta | 0.001357092495 | 0.00135709 | PASS |
| alpha recall positive intervals | 1 | 1 | PASS |
| alpha recall negative intervals | 0 | 0 | PASS |
| alpha recall overlap intervals | 35 | 35 | PASS |
| alpha mean FP delta | 1.581944444 | 1.581944 | PASS |
| alpha CI-count positive intervals | 36 | 36 | PASS |
| alpha complete-only mean F1 delta | -0.04152931449 | -0.0415293 | PASS |
| sample schedule p=20 gamma=1.0 | 1000 | 1000 | PASS |
| sample schedule p=20 gamma=1.25 | 796 | 796 | PASS |
| sample schedule p=50 gamma=1.0 | 2500 | 2500 | PASS |
| sample schedule p=50 gamma=1.25 | 2500 | 2500 | PASS |
| sample schedule p=75 gamma=1.0 | 3750 | 3750 | PASS |
| sample schedule p=75 gamma=1.25 | 4151 | 4151 | PASS |
| sample schedule p=100 gamma=1.0 | 5000 | 5000 | PASS |
| sample schedule p=100 gamma=1.25 | 5947 | 5947 | PASS |
| sample schedule p=150 gamma=1.0 | 7500 | 7500 | PASS |
| sample schedule p=150 gamma=1.25 | 9871 | 9871 | PASS |
| growth registered p>50 contrasts | 54 | 54 | PASS |
| growth p>50 mean F1 delta | 0.001264446432 | 0.00126445 | PASS |
| growth F1 positive intervals | 2 | 2 | PASS |
| growth F1 negative intervals | 0 | 0 | PASS |
| growth F1 overlap intervals | 52 | 52 | PASS |
| growth precision positive intervals | 0 | 0 | PASS |
| growth precision negative intervals | 0 | 0 | PASS |
| growth recall positive intervals | 4 | 4 | PASS |
| growth recall negative intervals | 0 | 0 | PASS |
| depth random_regular_d2 total | 50 | 50 | PASS |
| depth random_regular_d2 pass | 50 | 50 | PASS |
| depth small_world_k2 total | 40 | 40 | PASS |
| depth small_world_k2 pass | 40 | 40 | PASS |
| depth er_expected_degree_2 total | 50 | 50 | PASS |
| depth er_expected_degree_2 pass | 44 | 44 | PASS |
| depth scale_free_m2 total | 30 | 30 | PASS |
| depth scale_free_m2 pass | 0 | 0 | PASS |
| depth total pass | 134 | 134 | PASS |
| minimum complete-law true-edge query margin | 0.0002287597026 | 0.0002287597 | PASS |
| minimum selected-quadratic true-edge query margin | 0.0002085850191 | 0.000208585 | PASS |
| complete margins < .01 | 12 | 12 | PASS |
| selected margins < .01 | 13 | 13 | PASS |
| minimum selected quadratic retention diagnostic | 0.1684369243 | 0.1684369 | PASS |
| scale-free p20 complete F1 | 0.8054260004 | 0.805426 | PASS |
| scale-free p20 complete exact recovery | 0 | 0 | PASS |
| scale-free p20 self_masking_gaussian_preserving F1 | 0.7027646222 | 0.702765 | PASS |
| scale-free p20 self_masking_gaussian_preserving exact recovery | 0 | 0 | PASS |
| scale-free p50 complete F1 | 0.8247727933 | 0.824773 | PASS |
| scale-free p50 complete exact recovery | 0 | 0 | PASS |
| scale-free p50 self_masking_gaussian_preserving F1 | 0.7419762865 | 0.741976 | PASS |
| scale-free p50 self_masking_gaussian_preserving exact recovery | 0 | 0 | PASS |
| scale-free p75 complete F1 | 0.8425079875 | 0.842508 | PASS |
| scale-free p75 complete exact recovery | 0 | 0 | PASS |
| scale-free p75 self_masking_gaussian_preserving F1 | 0.7774157471 | 0.777416 | PASS |
| scale-free p75 self_masking_gaussian_preserving exact recovery | 0 | 0 | PASS |
| matched-local conditions | 24 | 24 | PASS |
| matched F1 intervals above zero | 3 | 3 | PASS |
| matched F1 intervals below zero | 11 | 11 | PASS |
| matched F1 overlap zero | 10 | 10 | PASS |
| matched precision intervals above zero | 0 | 0 | PASS |
| matched precision intervals below zero | 15 | 15 | PASS |
| matched recall intervals above zero | 6 | 6 | PASS |
| matched recall intervals below zero | 0 | 0 | PASS |
| matched single-target CI saving min | 0.9108428195 | 0.910843 | PASS |
| matched single-target CI saving max | 0.9695850816 | 0.969585 | PASS |
| matched batch CI saving min | 0.1084281953 | 0.108428 | PASS |
| matched batch CI saving max | 0.6958508163 | 0.695851 | PASS |
| matched batch CI saving positive all | 24 | 24 | PASS |
| matched batch runtime saving min | 0.1115336627 | 0.111534 | PASS |
| matched batch runtime saving max | 0.703010451 | 0.70301 | PASS |
| matched batch runtime CI wholly positive | 23 | 23 | PASS |
| matched paired F1 max half-width | 0.03178909283 | 0.031789 | PASS |

## Scope

This check validates the released empirical quantities used in the computational report together with the theorem-scope diagnostics. The 20-seed extension improves descriptive precision; paired inferential contrasts retain the original ten-seed design so that additional seeds do not silently redefine the inferential family.
