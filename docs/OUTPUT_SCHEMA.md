# Output schema and generated files

The experiment engine writes one directory per run or shard. The schema is intentionally rich so independent users can audit the scientific conditions, graph-recovery metrics, CI-query behavior, missingness calibration, and execution environment from the raw outputs.

## Per-run files

| File / directory | Purpose |
|---|---|
| `resolved_config.json` | Fully resolved scientific/execution settings |
| `environment.json` | Python/platform/package metadata |
| `results.csv` | Evaluation rows for completed graph cells |
| `failures.csv` | Failure records, present only when a cell fails |
| `metadata/` | Per-cell scientific/execution metadata |
| `traces/` | Optional full CI traces when `--trace-mode full` is requested |

The public VM scripts use `--trace-mode summary`; summary CI diagnostics are stored directly in `results.csv`.

## Key result columns

The complete smoke schema contains more than one hundred fields. The groups below identify the fields most useful for inspection.

### Scientific cell identity

- `cell_id`: transparent identifier derived from registered scientific settings;
- `topology`, `p`, `seed`;
- `gamma` and resolved sample-size fields;
- `missingness_mode`, `missing_rate_target`;
- `alpha_schedule`;
- `evaluation_scope` and, for target-level rows, `target`.

### Recovery metrics

- `precision`, `recall`, `f1`;
- `exact_recovery`;
- `tp`, `fp`, `fn`;
- normalized-error and deterministic-F1 audit fields.

### Search and usable-record diagnostics

- `trace_ci_tests`;
- `trace_ci_n_eff_min`, `trace_ci_n_eff_median`;
- `trace_ci_effective_fraction_mean`;
- conditioning-set summaries;
- insufficient/nonfinite decision fractions;
- `runtime_seconds`.

The historical raw-field names use `n_eff` / `effective_fraction`; throughout the public documentation these quantities are described as **usable records** for a CI query. The field names are retained for compatibility with the production-result lineage.

### Missingness diagnostics

- realized masked-cell and complete-row rates;
- population-calibration descriptors;
- quadratic/logistic mechanism parameters;
- selected-query retention diagnostics where applicable.

### Structural-interface diagnostics

- bounded-depth separator-premise fields;
- population edge-query partial-correlation margins;
- exact p=20 oracle-query diagnostics when enabled;
- explicit flags/skip reasons outside a diagnostic's scope.

## Cell status

`cell_status = complete` denotes a successfully completed graph cell. Merge and analysis scripts reject incomplete or duplicated registered cell sets. If a cell fails, the failure record contains the exception type/message and the VM scripts do not declare the shard complete.

## Analysis outputs

After `scripts/merge_and_analyze_campaign.sh`, each merged block contains an `analysis/` directory. Depending on the block, it includes:

- `summary.csv`: graph-level means and Student-t confidence intervals;
- `paired_contrasts.csv`: paired sample-growth, missingness, or alpha-schedule contrasts;
- `monte_carlo_precision.csv`: F1 half-width diagnostics by registered condition;
- `retention_summary.csv` and `retention_paired_contrasts.csv`;
- `matched_local_global_paired.csv`;
- `data_quality_checks.json`.

The precision-extension workflow additionally creates the combined seeds 0–19 analysis while retaining the seeds 0–9 inferential contrasts separately.

## Processed evidence

`analysis/reconstruct_evidence.py` maps completed experiment outputs into the 25-file released evidence tree under `evidence/`. `analysis/verify_evidence_reconstruction.py` compares a fresh reconstruction with the released reference, using exact text/JSON comparison and `1e-12` tolerance for numeric CSV fields.

## Reference artifacts

`analysis/generate_reference_artifacts.py` writes regenerated assets under:

```text
results/regenerated_artifacts/
```

The generated set contains six PDF figures, eight computational/result LaTeX tables, and a derived numerical grid for the information-rate calibration figure. `analysis/verify_reference_artifacts.py` checks those outputs against `reference/`.
