#!/usr/bin/env python3
"""Verify the small deterministic smoke run for the registered recovery engine.

This script is intentionally specific to the registered recovery pipeline.  It does
not rely on simplified smoke assumptions.  It validates graph-cell completeness,
fixed population mask calibration, evaluation-scope structure, finite metrics,
and the deterministic F1 lower-bound check.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path

import numpy as np
import pandas as pd

EXPECTED_MASKS = {
    "complete",
    "self_masking_gaussian_preserving",
    "self_masking_logistic_population",
}


def audit(results_csv: Path) -> dict:
    """Audit deterministic smoke output against the registered scientific invariants."""
    df = pd.read_csv(results_csv)
    required = {
        "cell_id", "cell_status", "evaluation_scope", "local_search_method",
        "missingness_mode", "mask_calibration", "targets_per_graph_realized",
        "f1", "precision", "recall", "deterministic_bound_verified",
        "trace_ci_nonfinite_fraction",
        "data_standardization", "missing_rate_target",
        "missing_rate_realized_masked_cells", "quadratic_a_realized",
        "quadratic_c_realized", "max_abs_complete_value",
        "ci_sanitizer_max_abs", "ci_sanitizer_clipping_inactive",
        "mask_variables", "masked_column_count", "p", "theorem_scope_class",
        "oracle_search_depth_premise_satisfied", "oracle_pc_query_diagnostics_run",
        "selected_edge_partial_corr_min", "selected_edge_query_retention_min",
        "selected_oracle_pc_dependent_partial_corr_min",
        "selected_oracle_pc_null_numeric_check",
        "selected_oracle_pc_query_retention_min",
    }
    missing_cols = sorted(required - set(df.columns))
    checks: dict[str, object] = {}
    checks["required_columns_present"] = not missing_cols
    checks["missing_columns"] = missing_cols
    if missing_cols:
        return {"pass": False, "checks": checks}

    cell_ids = df["cell_id"].dropna().astype(str)
    unique_cells = sorted(cell_ids.unique())
    checks["unique_graph_cells"] = len(unique_cells)
    checks["expected_six_graph_cells"] = len(unique_cells) == 6
    checks["all_complete"] = bool((df["cell_status"] == "complete").all())
    checks["expected_masking_modes"] = sorted(df["missingness_mode"].dropna().unique().tolist())
    checks["all_three_masking_modes_present"] = set(df["missingness_mode"].dropna()) == EXPECTED_MASKS
    checks["population_fixed_calibration_only"] = set(df["mask_calibration"].dropna()) == {"population_fixed"}
    checks["no_same_realization_standardization"] = set(df["data_standardization"].dropna()) == {"none_dedicated_population_sem_raw"}
    checks["all_query_coordinates_masked"] = set(df["mask_variables"].dropna()) == {"all"}
    checks["masked_column_count_equals_p"] = bool(
        (df["masked_column_count"].astype(int) == df["p"].astype(int)).all()
    )

    # Check the graph-level row once per generated cell. At smoke size this is
    # a Monte-Carlo tolerance check, not an exact equality requirement.
    graph_rows = df[df["evaluation_scope"] == "global_whole_skeleton"].copy()
    masked = graph_rows[graph_rows["missingness_mode"] != "complete"].copy()
    calibration_errors = (
        masked["missing_rate_realized_masked_cells"].astype(float)
        - masked["missing_rate_target"].astype(float)
    ).abs()
    checks["masked_rate_max_abs_error"] = float(calibration_errors.max()) if len(calibration_errors) else 0.0
    checks["masked_rate_within_smoke_tolerance"] = bool((calibration_errors <= 0.05).all())
    quadratic = graph_rows[graph_rows["missingness_mode"] == "self_masking_gaussian_preserving"]
    checks["quadratic_probability_valid"] = bool(
        len(quadratic) > 0
        and np.isfinite(quadratic["quadratic_a_realized"].astype(float)).all()
        and np.isfinite(quadratic["quadratic_c_realized"].astype(float)).all()
        and (quadratic["quadratic_a_realized"].astype(float) > 0).all()
        and (quadratic["quadratic_c_realized"].astype(float) <= 1.0 + 1e-12).all()
    )
    checks["quadratic_selected_edge_diagnostics_finite_positive"] = bool(
        len(quadratic) > 0
        and np.isfinite(quadratic["selected_edge_partial_corr_min"].astype(float)).all()
        and (quadratic["selected_edge_partial_corr_min"].astype(float) > 0).all()
        and np.isfinite(quadratic["selected_edge_query_retention_min"].astype(float)).all()
        and (quadratic["selected_edge_query_retention_min"].astype(float) > 0).all()
        and (quadratic["selected_edge_query_retention_min"].astype(float) <= 1.0).all()
    )
    q_oracle = quadratic[quadratic["oracle_pc_query_diagnostics_run"].astype("boolean").fillna(False).astype(bool)]
    checks["quadratic_selected_oracle_diagnostics_valid_when_run"] = bool(
        len(q_oracle) > 0
        and np.isfinite(q_oracle["selected_oracle_pc_dependent_partial_corr_min"].astype(float)).all()
        and (q_oracle["selected_oracle_pc_dependent_partial_corr_min"].astype(float) > 0).all()
        and q_oracle["selected_oracle_pc_null_numeric_check"].astype("boolean").fillna(False).astype(bool).all()
        and np.isfinite(q_oracle["selected_oracle_pc_query_retention_min"].astype(float)).all()
        and (q_oracle["selected_oracle_pc_query_retention_min"].astype(float) > 0).all()
    )
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
    checks["ci_sanitizer_clipping_inactive"] = bool(df["ci_sanitizer_clipping_inactive"].fillna(False).astype(bool).all())
    checks["finite_values_below_sanitizer_threshold"] = bool(
        (df["max_abs_complete_value"].astype(float) < df["ci_sanitizer_max_abs"].astype(float)).all()
    )
    checks["no_dedicated_local_rows"] = not bool((df["evaluation_scope"] == "dedicated_local").any())
    checks["local_method_none_only"] = set(df["local_search_method"].dropna()) == {"none"}

    finite_cols = ["f1", "precision", "recall", "trace_ci_nonfinite_fraction"]
    checks["finite_key_metrics"] = bool(np.isfinite(df[finite_cols].to_numpy(dtype=float)).all())
    checks["zero_nonfinite_ci_fraction"] = bool((df["trace_ci_nonfinite_fraction"].fillna(0) == 0).all())
    checks["deterministic_f1_bound_all_verified"] = bool(df["deterministic_bound_verified"].fillna(False).astype(bool).all())

    structures = []
    complete_structure = True
    for cell_id, group in df.groupby("cell_id", sort=True):
        realized = int(group["targets_per_graph_realized"].iloc[0])
        counts = group["evaluation_scope"].value_counts().to_dict()
        ok = (
            counts.get("global_whole_skeleton", 0) == 1
            and counts.get("target_restriction_of_global", 0) == realized
            and counts.get("dedicated_local", 0) == 0
            and len(group) == 1 + realized
        )
        complete_structure &= ok
        structures.append({
            "cell_id": str(cell_id),
            "targets_per_graph_realized": realized,
            "rows": int(len(group)),
            "scope_counts": {str(k): int(v) for k, v in counts.items()},
            "structure_ok": bool(ok),
        })
    checks["all_graph_cells_have_expected_scope_structure"] = bool(complete_structure)
    checks["cell_structures"] = structures

    # A graph-level cell_id must identify one unique experimental condition;
    # multiple output rows are expected because target restrictions share it.
    condition_cols = [
        "p", "n", "gamma", "topology", "sem_model", "missingness_mode",
        "missing_rate_target", "alpha_schedule", "d_alg", "seed",
    ]
    condition_cols = [c for c in condition_cols if c in df.columns]
    ambiguous = []
    for cell_id, group in df.groupby("cell_id", sort=True):
        unique_conditions = group[condition_cols].drop_duplicates()
        if len(unique_conditions) != 1:
            ambiguous.append(str(cell_id))
    checks["cell_ids_map_to_unique_graph_conditions"] = len(ambiguous) == 0
    checks["ambiguous_cell_ids"] = ambiguous

    boolean_gates = [
        "required_columns_present",
        "expected_six_graph_cells",
        "all_complete",
        "all_three_masking_modes_present",
        "population_fixed_calibration_only",
        "no_same_realization_standardization",
        "all_query_coordinates_masked",
        "masked_column_count_equals_p",
        "masked_rate_within_smoke_tolerance",
        "quadratic_probability_valid",
        "quadratic_selected_edge_diagnostics_finite_positive",
        "quadratic_selected_oracle_diagnostics_valid_when_run",
        "theorem_scope_class_consistent",
        "ci_sanitizer_clipping_inactive",
        "finite_values_below_sanitizer_threshold",
        "no_dedicated_local_rows",
        "local_method_none_only",
        "finite_key_metrics",
        "zero_nonfinite_ci_fraction",
        "deterministic_f1_bound_all_verified",
        "all_graph_cells_have_expected_scope_structure",
        "cell_ids_map_to_unique_graph_conditions",
    ]
    passed = all(bool(checks[k]) for k in boolean_gates)
    return {"pass": passed, "results_csv": str(results_csv), "rows": int(len(df)), "checks": checks}


def main() -> int:
    """Run the strict smoke-result audit and write its machine-readable report."""
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument(
        "--results",
        default="results/global_smoke/results.csv",
        help="Path to smoke-test results.csv",
    )
    parser.add_argument(
        "--out",
        default="smoke_verification.json",
        help="JSON verification output path",
    )
    parser.add_argument(
        "--verbose",
        action="store_true",
        help="Print the complete JSON audit in addition to writing it to --out.",
    )
    args = parser.parse_args()
    result = audit(Path(args.results))
    Path(args.out).write_text(
        json.dumps(result, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    if args.verbose:
        print(json.dumps(result, indent=2, sort_keys=True))
    else:
        verdict = "PASS" if result["pass"] else "FAIL"
        print(
            f"Smoke integrity audit: {verdict} "
            f"({result['rows']} rows; report: {args.out})"
        )
    return 0 if result["pass"] else 2


if __name__ == "__main__":
    raise SystemExit(main())
