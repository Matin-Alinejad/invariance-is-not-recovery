#!/usr/bin/env python3
"""Verify a merged experiment block against its registered scientific design.

The checks cover registered cells, row structure, masking calibration, SEM
parameter invariance, pinned package versions, and theorem-scope diagnostics.
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path
from typing import Any

import numpy as np
import pandas as pd
import yaml

REPO_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO_ROOT / "code"))

from experiments.run_recovery_experiments import expand_specs  # noqa: E402


def _json_canonical(obj: Any) -> str:
    return json.dumps(obj, sort_keys=True, separators=(",", ":"), default=str)


def _metadata_sem_signature(path: Path) -> str:
    obj = json.loads(path.read_text(encoding="utf-8"))
    return _json_canonical(obj.get("causal_parameters", {}))


def _locked_versions(path: Path) -> dict[str, str]:
    """Parse exact ``name==version`` pins from the frozen requirements lock."""
    pins: dict[str, str] = {}
    for raw in path.read_text(encoding="utf-8").splitlines():
        line = raw.strip()
        if not line or line.startswith("#") or "==" not in line:
            continue
        name, version = line.split("==", 1)
        pins[re.sub(r"[-_.]+", "-", name.strip().lower())] = version.strip()
    return pins


def _canon_package(name: str) -> str:
    return re.sub(r"[-_.]+", "-", str(name).strip().lower())


def audit(config_path: Path, results_dir: Path) -> dict[str, Any]:
    """Audit a merged result directory against its registered configuration and invariants."""
    config = yaml.safe_load(config_path.read_text(encoding="utf-8"))
    expected_specs = expand_specs(config, quick=False)
    expected_ids = {str(x["cell_id"]) for x in expected_specs}

    results_path = results_dir / "results.csv"
    if not results_path.exists():
        return {"pass": False, "error": f"missing {results_path}"}
    df = pd.read_csv(results_path)
    checks: dict[str, Any] = {}

    required = {
        "cell_id", "cell_status", "evaluation_scope", "targets_per_graph_realized",
        "local_search_method", "mask_calibration",
        "data_standardization", "ci_sanitizer_clipping_inactive",
        "trace_ci_nonfinite_fraction", "deterministic_bound_verified",
        "missingness_mode", "missing_rate_target", "missing_rate_realized_masked_cells",
        "topology", "p", "gamma", "seed", "alpha_schedule",
        "oracle_search_depth_premise_satisfied", "oracle_separator_coverage_fraction", "oracle_depth_audit_mode",
        "mask_variables", "masked_column_count", "theorem_scope_class",
        "selected_edge_partial_corr_min", "selected_edge_query_retention_min",
        "selected_edge_diagnostics_finite",
    }
    missing_cols = sorted(required - set(df.columns))
    checks["required_columns_present"] = not missing_cols
    checks["missing_columns"] = missing_cols
    if missing_cols:
        return {"pass": False, "checks": checks}

    complete = df[df["cell_status"] == "complete"].copy()
    observed_ids = set(complete["cell_id"].dropna().astype(str).unique())
    checks["expected_registered_cells"] = len(expected_ids)
    checks["observed_complete_cells"] = len(observed_ids)
    checks["exact_registered_cell_set"] = observed_ids == expected_ids
    checks["missing_registered_cells"] = sorted(expected_ids - observed_ids)[:50]
    checks["unexpected_cells"] = sorted(observed_ids - expected_ids)[:50]
    checks["failed_result_rows"] = int((df["cell_status"] != "complete").sum())
    checks["no_failed_result_rows"] = checks["failed_result_rows"] == 0



    # Scope structure per generated graph cell.
    bad_structure: list[str] = []
    for cell_id, group in complete.groupby("cell_id", sort=False):
        realized = int(group["targets_per_graph_realized"].iloc[0])
        local_method = str(group["local_search_method"].iloc[0])
        expected_local = 0 if local_method == "none" else realized
        counts = group["evaluation_scope"].value_counts()
        ok = (
            counts.get("global_whole_skeleton", 0) == 1
            and counts.get("target_restriction_of_global", 0) == realized
            and counts.get("dedicated_local", 0) == expected_local
            and len(group) == 1 + realized + expected_local
        )
        if not ok:
            bad_structure.append(str(cell_id))
    checks["scope_structure_valid"] = not bad_structure
    checks["bad_scope_cells"] = bad_structure[:50]

    checks["population_fixed_calibration_only"] = set(complete["mask_calibration"].dropna()) == {"population_fixed"}
    checks["no_same_realization_standardization"] = set(complete["data_standardization"].dropna()) == {"none_dedicated_population_sem_raw"}
    checks["all_query_coordinates_masked"] = set(complete["mask_variables"].dropna()) == {"all"}
    checks["masked_column_count_equals_p"] = bool(
        (complete["masked_column_count"].astype(int) == complete["p"].astype(int)).all()
    )
    checks["ci_sanitizer_clipping_inactive"] = bool(complete["ci_sanitizer_clipping_inactive"].fillna(False).astype(bool).all())
    checks["zero_nonfinite_ci_fraction"] = bool((complete["trace_ci_nonfinite_fraction"].fillna(0).astype(float) == 0).all())
    checks["deterministic_f1_bound_verified"] = bool(complete["deterministic_bound_verified"].fillna(False).astype(bool).all())

    # Mask calibration is probabilistic per finite realization. Audit mean bias
    # over graph cells, not an unrealistic per-cell equality to the target.
    graph_rows = complete[complete["evaluation_scope"] == "global_whole_skeleton"].copy()
    quadratic_rows = graph_rows[graph_rows["missingness_mode"] == "self_masking_gaussian_preserving"].copy()
    quadratic_covered = quadratic_rows[
        quadratic_rows["oracle_search_depth_premise_satisfied"].fillna(False).astype(bool)
    ].copy()
    quadratic_stress = quadratic_rows[
        ~quadratic_rows["oracle_search_depth_premise_satisfied"].fillna(False).astype(bool)
    ].copy()
    # Selected-law margin diagnostics are intentionally computed only where the
    # bounded-depth search premise holds. Stress graphs exit the structural audit
    # at a certified failure witness, so requiring expensive margin enumeration
    # there would add cost without making them theorem-covered.
    checks["quadratic_selected_edge_diagnostics_valid"] = bool(
        len(quadratic_covered) > 0
        and quadratic_covered["selected_edge_diagnostics_finite"].eq(True).all()
        and np.isfinite(quadratic_covered["selected_edge_partial_corr_min"].astype(float)).all()
        and (quadratic_covered["selected_edge_partial_corr_min"].astype(float) > 0).all()
        and np.isfinite(quadratic_covered["selected_edge_query_retention_min"].astype(float)).all()
        and (quadratic_covered["selected_edge_query_retention_min"].astype(float) > 0).all()
        and (quadratic_covered["selected_edge_query_retention_min"].astype(float) <= 1.0).all()
        and quadratic_stress["selected_edge_diagnostics_finite"].isna().all()
        and quadratic_stress["selected_edge_partial_corr_min"].isna().all()
        and quadratic_stress["selected_edge_query_retention_min"].isna().all()
    )
    checks["quadratic_depth_covered_cells"] = int(len(quadratic_covered))
    checks["quadratic_depth_stress_cells"] = int(len(quadratic_stress))
    expected_scope = graph_rows.apply(
        lambda r: (
            "distribution_and_depth_stress" if (r["missingness_mode"] == "self_masking_logistic_population" and not bool(r["oracle_search_depth_premise_satisfied"]))
            else "distribution_stress" if r["missingness_mode"] == "self_masking_logistic_population"
            else "depth_stress" if not bool(r["oracle_search_depth_premise_satisfied"])
            else "gaussian_preserving_depth_covered"
        ), axis=1
    )
    checks["theorem_scope_class_consistent"] = bool(
        (graph_rows["theorem_scope_class"].astype(str).to_numpy() == expected_scope.astype(str).to_numpy()).all()
    )
    mask_summary = []
    calibration_mean_ok = True
    for (mode, target_rate), g in graph_rows.groupby(["missingness_mode", "missing_rate_target"], sort=True, dropna=False):
        target = float(target_rate)
        realized = float(g["missing_rate_realized_masked_cells"].mean())
        err = abs(realized - target)
        mask_summary.append({
            "mode": str(mode), "target_rate": target, "graph_cells": int(len(g)),
            "realized_mean": realized, "absolute_mean_error": err,
        })
        tol = 1e-12 if str(mode) == "complete" else 0.01
        calibration_mean_ok &= err <= tol
    checks["mask_calibration_summary"] = mask_summary
    checks["mask_calibration_mean_within_tolerance"] = bool(calibration_mean_ok)

    # Metadata-level structural-parameter invariance. All cells that share
    # topology,p,seed must have the same SEM, regardless of gamma/mask/alpha.
    metadata_dir = results_dir / "metadata"
    missing_metadata: list[str] = []
    sem_by_condition: dict[tuple[str, int, int], set[str]] = {}
    global_conditions = graph_rows[["cell_id", "topology", "p", "seed"]].drop_duplicates()
    for row in global_conditions.itertuples(index=False):
        path = metadata_dir / f"{row.cell_id}.json"
        if not path.exists():
            missing_metadata.append(str(row.cell_id))
            continue
        sig = _metadata_sem_signature(path)
        key = (str(row.topology), int(row.p), int(row.seed))
        sem_by_condition.setdefault(key, set()).add(sig)
    drift = [list(key) for key, sigs in sem_by_condition.items() if len(sigs) != 1]
    checks["metadata_complete"] = not missing_metadata
    checks["missing_metadata_cells"] = missing_metadata[:50]
    checks["matched_sem_parameter_invariance"] = not drift
    checks["sem_drift_conditions"] = drift[:50]

    # Dependency/environment contract. Each returned shard records package
    # versions; all scientific packages must match the exact public lock file.
    lock_path = REPO_ROOT / "requirements-lock.txt"
    locked = _locked_versions(lock_path)
    shard_env_path = results_dir / "shard_environments.json"
    env_problems: list[dict[str, Any]] = []
    checked_envs = 0
    if shard_env_path.exists():
        shard_envs = json.loads(shard_env_path.read_text(encoding="utf-8"))
        for shard, env in sorted(shard_envs.items()):
            checked_envs += 1
            packages = {_canon_package(k): str(v) for k, v in env.get("packages", {}).items()}
            for pkg in [
                "numpy", "pandas", "scipy", "scikit-learn", "networkx",
                "matplotlib", "joblib", "pyyaml", "pytest", "statsmodels",
                "threadpoolctl",
            ]:
                expected = locked.get(_canon_package(pkg))
                observed = packages.get(_canon_package(pkg))
                if expected is not None and observed != expected:
                    env_problems.append({
                        "shard": shard, "reason": "package_version_mismatch",
                        "package": pkg, "expected": expected, "observed": observed,
                    })
    checks["shard_environment_records_present"] = shard_env_path.exists() and checked_envs > 0
    checks["shard_environment_count"] = int(checked_envs)
    checks["locked_scientific_packages_match"] = len(env_problems) == 0 and checked_envs > 0
    checks["environment_problems"] = env_problems[:50]

    # Theorem-scope reporting. These are descriptive strata, not all-or-nothing
    # evidence gates: the registered suite deliberately includes stress regimes.
    graph_struct = graph_rows.drop_duplicates(["topology", "p", "seed"])
    depth_ok = graph_struct["oracle_search_depth_premise_satisfied"].fillna(False).astype(bool)
    checks["unique_graph_structures"] = int(len(graph_struct))
    checks["depth_premise_satisfied_graphs"] = int(depth_ok.sum())
    checks["depth_premise_stress_graphs"] = int((~depth_ok).sum())
    depth_table = (
        graph_struct.groupby(["topology", "p"], dropna=False)
        .agg(
            graphs=("seed", "size"),
            depth_premise_satisfied=("oracle_search_depth_premise_satisfied", "sum"),
            exhaustive_passes=("oracle_depth_audit_mode", lambda x: int((x.astype(str) == "exhaustive_pass").sum())),
            certified_failure_witnesses=("oracle_depth_audit_mode", lambda x: int((x.astype(str) == "early_exit_failure_witness").sum())),
        )
        .reset_index()
    )
    checks["depth_scope_table"] = depth_table.to_dict(orient="records")

    if "oracle_pc_query_diagnostics_run" in graph_struct.columns:
        q = graph_struct[graph_struct["oracle_pc_query_diagnostics_run"].fillna(False).astype(bool)].copy()
        checks["oracle_query_diagnostic_graphs"] = int(len(q))
        if len(q):
            if "oracle_pc_null_numeric_check" in q:
                checks["oracle_null_numeric_all"] = bool(q["oracle_pc_null_numeric_check"].fillna(False).astype(bool).all())
            if "oracle_pc_exact_skeleton" in q:
                checks["oracle_exact_skeleton_graphs"] = int(q["oracle_pc_exact_skeleton"].fillna(False).astype(bool).sum())
                checks["oracle_inexact_skeleton_graphs"] = int((~q["oracle_pc_exact_skeleton"].fillna(False).astype(bool)).sum())

    # Merge audit consistency when available.
    merge_path = results_dir / "merge_report.json"
    if merge_path.exists():
        merge = json.loads(merge_path.read_text(encoding="utf-8"))
        checks["merge_report_present"] = True
        checks["merge_unique_cells_matches"] = int(merge.get("unique_cells", -1)) == len(expected_ids)
        checks["merge_failures_zero"] = int(merge.get("failures", -1)) == 0
    else:
        checks["merge_report_present"] = False
        checks["merge_unique_cells_matches"] = False
        checks["merge_failures_zero"] = False

    hard_gates = [
        "required_columns_present", "exact_registered_cell_set", "no_failed_result_rows",
        "scope_structure_valid",
        "population_fixed_calibration_only", "no_same_realization_standardization",
        "all_query_coordinates_masked", "masked_column_count_equals_p",
        "quadratic_selected_edge_diagnostics_valid", "theorem_scope_class_consistent",
        "ci_sanitizer_clipping_inactive", "zero_nonfinite_ci_fraction",
        "deterministic_f1_bound_verified", "mask_calibration_mean_within_tolerance",
        "metadata_complete", "matched_sem_parameter_invariance",
        "shard_environment_records_present", "locked_scientific_packages_match",
        "merge_report_present", "merge_unique_cells_matches", "merge_failures_zero",
    ]
    passed = all(bool(checks.get(k, False)) for k in hard_gates)
    return {
        "pass": passed,
        "config": str(config_path),
        "results_dir": str(results_dir),
        "hard_gates": hard_gates,
        "checks": checks,
    }


def main() -> int:
    """Run the strict merged-result integrity audit and emit a machine-readable report."""
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--config", required=True)
    ap.add_argument("--results-dir", required=True)
    ap.add_argument("--out", required=True)
    args = ap.parse_args()
    result = audit(Path(args.config), Path(args.results_dir))
    Path(args.out).parent.mkdir(parents=True, exist_ok=True)
    Path(args.out).write_text(json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0 if result["pass"] else 2


if __name__ == "__main__":
    raise SystemExit(main())
