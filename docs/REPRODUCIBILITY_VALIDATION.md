# Reproducibility validation record

This document records the checks used to seal the public repository. It complements the executable gate in `scripts/verify_release.sh` and distinguishes lightweight release verification from the expensive full experiment campaign.

## Public release gate

From a clean repository tree, `bash scripts/verify_release.sh` performs the following checks:

1. `PYTHONPATH=code python -m pytest -q tests` → **26/26 scientific/regression tests pass**.
2. `python analysis/verify_reported_results.py` → **121/121 reported-result checks pass**, including 10 direct checks of the production integer sample-size schedule.
3. `python analysis/verify_reference_artifacts.py` → **6/6 generated figures match the references by rendered-pixel equality**, **8/8 computational/result LaTeX tables match byte-for-byte**, and the native TikZ schematic is present.
4. `bash scripts/run_global_smoke.sh` → **6 graph cells, 48 rows**, strict global/restricted-global smoke audit **PASS**.
5. `bash scripts/run_target_local_smoke.sh` → **3 graph cells, 12 dedicated-local rows**, finite target-level precision/recall/F1 **PASS**.
6. Python byte-compilation, public CLI `--help` checks, and Bash syntax checks pass.
7. The shipped `.lean` files contain no `sorry` or `admit` terms.
8. The public tree is checked for machine-specific paths, checksum/fingerprint machinery, and generated cache debris.

## Production-lineage equivalence audit

The archived VM experiment engine and the public engine were executed independently on the same deterministic six-cell smoke design.

- archived VM output: **48 × 153**;
- public output: **48 × 152**;
- the removed archived-only column was non-scientific execution bookkeeping;
- all 48 rows align one-to-one by scientific condition;
- the human-readable public `cell_id` intentionally differs from the archived opaque identifier;
- five timing fields vary because the two runs were executed separately;
- after excluding those identifier/timing fields, the remaining **146 common scientific fields match exactly**, with numeric tolerance `1e-12`.

This check verifies that public naming/documentation cleanup did not change graph generation, SEM parameters, random streams, masking, CI decisions, search outputs, or scientific diagnostics on the deterministic provenance design.

## Sample-size schedule closure

The production engine owns the integer schedule through `calibrated_sample_size(...)` in `code/experiments/run_recovery_experiments.py`. The reference artifact generator imports that exact helper and reads `reference_p` / `reference_n_over_p` from `configs/primary_scaling.yaml`.

For `gamma = 1.25`, the registered integer sample sizes at `p = 20, 50, 75, 100, 150` are:

```text
796, 2500, 4151, 5947, 9871
```

The regression suite and `analysis/verify_reported_results.py` both assert this schedule. No second rounding implementation is maintained in the artifact layer.

## Diagnostic regeneration audit

The release-sealing audit regenerates the finite-grid structural diagnostics from the fixed primary configuration and public scientific source:

- `depth_scope.csv`: **170 × 19**;
- `population_margins.csv`: **170 × 26**;
- `p20_oracle_queries.csv`: **40 × 28**.

Numeric comparisons use tolerance `1e-12`; text fields and schemas must agree exactly.

## Reference artifact audit

The reference artifact generator reads the released processed evidence and reconstructs the computational assets. The seal check verifies:

- six generated PDF figures by rendered-pixel equality at 120 dpi;
- eight generated computational/result LaTeX tables byte-for-byte;
- the recovery-pipeline schematic as native LaTeX/TikZ source.

The two explanatory tables (notation guide and formalization-scope map) are maintained as document-native semantic tables rather than reconstructed from experiment evidence; see `docs/RESULT_PROVENANCE_MAP.md`.

## Distributed precision-extension workflow audit

The seeds 10–19 extension workflow was exercised end-to-end on a reduced sharded campaign:

1. four primary shards;
2. four non-overlapping extension shards;
3. strict merge and integrity audit;
4. seed-set overlap check;
5. combination of seeds 0–9 and 10–19;
6. graph-level summary and Monte Carlo precision analysis.

The production scripts used for the full campaign are the same public entry points documented in the README.

## Full-campaign boundary

The complete **2,760-cell** distributed campaign is intentionally not rerun by the lightweight release gate. The repository instead provides the fixed route for an independent full rerun:

1. four-VM experiment sharding;
2. strict merge and block audits;
3. non-overlapping seeds 10–19 precision extension;
4. extension merge and 20-seed combination;
5. structural/population/oracle diagnostics;
6. reconstruction of the 25-file processed evidence bundle;
7. comparison with the released evidence;
8. 121 reported-result checks;
9. six-figure/eight-computational-table regeneration and equivalence verification.

After the registered computations are complete, run:

```bash
N_JOBS=8 bash scripts/reconstruct_release_results.sh
```

The reference campaign used four Ubuntu VMs, each with **32 vCPUs, 64 GB RAM, and 200 GB local disk**, using **8 Python workers per VM**.

The lightweight Python release gate does not perform a fresh Lean/Mathlib compilation. The pinned Lean projects and `formal/build_all.sh` are shipped for that purpose.
