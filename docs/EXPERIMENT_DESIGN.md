# Experiment design

This document summarizes the fixed computational design encoded in `configs/*.yaml`. The YAML files and the production experiment engine are the executable source of truth; this document provides the corresponding human-readable contract.

## Common design

Unless a block explicitly overrides a setting, the experiments use:

| Setting | Value |
|---|---|
| SEM family | sparse linear-Gaussian |
| Structural coefficient magnitudes | uniform on `[0.5, 1.0]` with random signs |
| Innovation noise | iid Gaussian, mean 0, standard deviation 1 |
| CI test | Pearson partial correlation / Student-t calibration |
| Maximum conditioning-set size | `d_alg = 3` |
| Minimum usable records per CI query | 10 |
| Insufficient-record policy | keep the edge |
| Missing-data handling | test-wise deletion |
| Masked variables | all variables in registered self-masking regimes |
| Population masking slope | 1.0 |
| Quadratic masking base parameter | 0.2 |
| Target selection when enabled | deterministic degree-stratified |
| Targets per graph | 10 |
| Reference scaling constants | `reference_p = 50`, `reference_n_over_p = 50` |

## Sample-size schedule

The production runner defines the sample size through `calibrated_sample_size(...)` in `code/experiments/run_recovery_experiments.py`:

```text
constant = reference_n_over_p * reference_p ** (1 - gamma)
n = ceil(constant * p ** gamma)
```

With the registered values `reference_p = 50` and `reference_n_over_p = 50`, this is

```text
n(p, gamma) = ceil(2500 * (p / 50) ** gamma),   gamma in {1.0, 1.25}.
```

The resulting integer schedule is:

| `p` | `gamma = 1.0` | `gamma = 1.25` |
| ---: | ---: | ---: |
| 20 | 1000 | 796 |
| 50 | 2500 | 2500 |
| 75 | 3750 | 4151 |
| 100 | 5000 | 5947 |
| 150 | 7500 | 9871 |

These values are regression-tested so documentation and generated reference tables cannot silently diverge from the production engine.

## Primary scaling block

Configuration: `configs/primary_scaling.yaml`

- seeds: 0–9;
- `gamma ∈ {1.0, 1.25}`;
- alpha schedule: `n_inverse_half`;
- missingness modes: complete, Gaussian-preserving quadratic self-masking, population-calibrated logistic self-masking;
- target missing rate: 0 for complete data and 0.3 for the self-masking regimes;
- dedicated local search disabled.

Topology/dimension support:

| Topology | Parameters | Dimensions |
|---|---|---|
| random regular | degree 2 | 20, 50, 75, 100, 150 |
| Erdős–Rényi | expected degree 2 | 20, 50, 75, 100, 150 |
| small world | `k=2`, rewiring probability 0.1 | 20, 50, 75, 100 |
| scale free | `m=2` | 20, 50, 75 |

Total: **1,020 graph cells**.

## Primary precision extension

Configuration: `configs/primary_scaling_precision_extension.yaml`

This block repeats the primary design with non-overlapping seeds **10–19**. Its role is descriptive Monte Carlo precision. The original paired inferential family remains based on seeds 0–9.

Total: **1,020 graph cells**.

## Significance-threshold sensitivity

Configuration: `configs/significance_threshold_sensitivity.yaml`

- seeds: 0–9;
- dimensions: 50 and 100;
- topologies: random regular, Erdős–Rényi, small world;
- `gamma = 1.0`;
- alpha schedules: `n_inverse_half` and `fixed_005`;
- complete, quadratic self-masking, and logistic self-masking conditions.

Total: **360 graph cells**.

## Retention sensitivity

Configuration: `configs/retention_sensitivity.yaml`

- seeds: 0–9;
- dimensions: 50 and 100;
- topologies: random regular and small world;
- `gamma = 1.0`;
- Gaussian-preserving quadratic self-masking;
- target missing rates: 0.1, 0.3, 0.5.

Total: **120 graph cells**.

## Matched target-local/global study

Configuration: `configs/matched_local_global.yaml`

- seeds: 0–9;
- dimensions: 20 and 50;
- topologies: random regular, Erdős–Rényi, small world, scale free;
- `gamma = 1.0`;
- complete, quadratic self-masking, and logistic self-masking conditions;
- 10 deterministic degree-stratified targets per generated graph;
- both the global fit restricted to the target neighborhood and the dedicated target-local search are reported.

Total: **240 graph cells**.

The comparison is matched on the same graph, sample, mask realization, target set, and evaluation edge set. Cost is reported both for one target and for the prespecified batch of targets, because a global fit is paid once while a dedicated-local fit is paid once per target.

## Deterministic coupling and random streams

The production generator deliberately separates random streams for graph structure, SEM parameters, observation noise, and missingness. For a fixed graph/seed:

- structural coefficients do not depend on sample size;
- the smaller sample is an exact row prefix of the larger sample;
- matched missingness conditions use aligned mask-uniform prefixes;
- no sample-fitted standardization is performed before masking.

These invariants are regression-tested in `tests/test_experiment_population_alignment.py` and related tests.

## Evaluation scopes

The output column `evaluation_scope` distinguishes three estimands:

- `global_whole_skeleton`: precision/recall/F1 over the full undirected skeleton;
- `target_restriction_of_global`: target-incident edges extracted from the global estimate;
- `dedicated_local`: target-incident edges returned by the dedicated target-local search.

The dedicated-local branch is used only in the matched local/global block.

## Structural diagnostics

The reconstruction workflow separately measures:

- bounded-depth separator coverage (`measure_search_depth_scope.py`);
- population edge-query partial-correlation margins and selected-query retention (`measure_population_margins.py`);
- exact p=20 oracle-PC query margins (`measure_p20_oracle_queries.py`);
- finite-state selection identity and randomized oracle-search stress checks.

These diagnostics characterize the registered finite grid and the theorem/experiment interface; they are not dimension-uniform strong-faithfulness statements.
