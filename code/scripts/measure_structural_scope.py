#!/usr/bin/env python3
"""Compute theorem-scope diagnostics for each unique primary graph/SEM structure.

This diagnostic is independent of Monte Carlo recovery outcomes. It verifies the
registered bounded-depth search premise and, when that premise holds, computes
population partial-correlation and selected-law diagnostics from the fixed SEM
parameters. Failed depth audits return a concrete nonedge witness; no pseudo
coverage fraction is reported for those stress cases.
"""
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

import numpy as np
import pandas as pd
import yaml
from joblib import Parallel, delayed

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "code"))

from experiments.run_recovery_experiments import expand_specs, topology_spec
from src.algorithms.population_calibrated_missingness import choose_quadratic_a
from src.data_generation.linear_gaussian_sem import generate_graph, generate_linear_gaussian_sample
from src.data_generation.sem_diagnostics import (
    edge_partial_correlation_margin,
    linear_sem_covariance,
    oracle_pc_query_margin_diagnostics,
    pc_separator_depth_diagnostics,
    quadratic_selected_edge_query_diagnostics,
)


def _empty_edge_diagnostics() -> dict:
    return {
        "oracle_edge_query_count": np.nan,
        "oracle_edge_partial_corr_min": np.nan,
        "oracle_edge_partial_corr_q10": np.nan,
        "oracle_edge_partial_corr_median": np.nan,
        "oracle_edge_partial_corr_below_001": np.nan,
        "oracle_edge_partial_corr_below_005": np.nan,
        "oracle_edge_partial_corr_below_010": np.nan,
        "oracle_edge_margin_finite": np.nan,
    }


def _empty_selected_diagnostics() -> dict:
    return {
        "selected_edge_query_count": np.nan,
        "selected_edge_partial_corr_min": np.nan,
        "selected_edge_partial_corr_q10": np.nan,
        "selected_edge_partial_corr_median": np.nan,
        "selected_edge_partial_corr_max": np.nan,
        "selected_edge_partial_corr_below_001": np.nan,
        "selected_edge_partial_corr_below_005": np.nan,
        "selected_edge_partial_corr_below_010": np.nan,
        "selected_edge_query_retention_min": np.nan,
        "selected_edge_query_retention_q10": np.nan,
        "selected_edge_query_retention_median": np.nan,
        "selected_edge_query_retention_max": np.nan,
        "selected_edge_diagnostics_finite": np.nan,
    }


def _audit_one(spec: dict, quadratic_a: float, quadratic_c: float) -> dict:
    p = int(spec["p"])
    seed = int(spec["seed"])
    depth = int(spec["max_conditioning_set_size"])
    topology, params = topology_spec(spec["topology_entry"], p)

    graph = generate_graph(topology, p, params, seed)
    generated = generate_linear_gaussian_sample(
        graph=graph,
        n_samples=2,
        seed=seed,
        signal_low=float(spec["signal_low"]),
        signal_high=float(spec["signal_high"]),
    )
    nodes, covariance = linear_sem_covariance(graph, generated.causal_parameters)

    depth_report = pc_separator_depth_diagnostics(graph, depth)
    depth_ok = bool(depth_report["oracle_search_depth_premise_satisfied"])
    if depth_ok:
        edge_diagnostics = edge_partial_correlation_margin(
            graph,
            covariance,
            nodes,
            depth,
        )
        selected_diagnostics = quadratic_selected_edge_query_diagnostics(
            graph,
            covariance,
            nodes,
            depth,
            masked_nodes=set(map(str, graph.nodes())),
            quadratic_a=quadratic_a,
            quadratic_c=quadratic_c,
        )
    else:
        edge_diagnostics = _empty_edge_diagnostics()
        selected_diagnostics = _empty_selected_diagnostics()

    row = {
        "topology": spec["topology_name"],
        "p": p,
        "seed": seed,
        "d_alg": depth,
        "true_edges": int(graph.number_of_edges()),
        **depth_report,
        **edge_diagnostics,
        **selected_diagnostics,
    }

    query_limit = int(spec.get("oracle_query_diagnostics_max_p", 20))
    if p <= query_limit and depth_ok:
        row.update(
            oracle_pc_query_margin_diagnostics(
                graph,
                covariance,
                nodes,
                depth,
                selected_quadratic_masked_nodes=set(map(str, graph.nodes())),
                selected_quadratic_a=quadratic_a,
                selected_quadratic_c=quadratic_c,
            )
        )
        row["oracle_pc_query_diagnostics_run"] = True
        row["oracle_pc_query_diagnostics_skip_reason"] = ""
    else:
        row["oracle_pc_query_diagnostics_run"] = False
        row["oracle_pc_query_diagnostics_skip_reason"] = (
            "depth_premise_false"
            if not depth_ok
            else "p_above_exact_query_audit_limit"
        )
    return row


def _unique_specs(config: dict) -> dict[tuple, dict]:
    unique: dict[tuple, dict] = {}
    for spec in expand_specs(config, quick=False):
        key = (
            spec["topology_name"],
            int(spec["p"]),
            int(spec["seed"]),
            float(spec["signal_low"]),
            float(spec["signal_high"]),
            int(spec["max_conditioning_set_size"]),
        )
        unique.setdefault(key, spec)
    return unique


def _count_depth_failures(values: pd.Series) -> int:
    return int((values.astype(str) == "early_exit_failure_witness").sum())


def main() -> int:
    """Run the full structural-scope diagnostic over the registered primary design."""
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--config", default="configs/primary_scaling.yaml")
    parser.add_argument("--csv", default="primary_structural_scope.csv")
    parser.add_argument("--json", default="primary_structural_scope.json")
    parser.add_argument("--n-jobs", type=int, default=8)
    args = parser.parse_args()

    config = yaml.safe_load((ROOT / args.config).read_text())
    unique = _unique_specs(config)

    target_retention = 1.0 - 0.30
    quadratic_a = choose_quadratic_a(
        target_retention,
        float(config["base"].get("quadratic_a", 0.2)),
    )
    quadratic_c = target_retention * np.sqrt(1.0 + quadratic_a)

    ordered_specs = [spec for _, spec in sorted(unique.items())]
    rows = Parallel(n_jobs=max(1, args.n_jobs), backend="loky", verbose=0)(
        delayed(_audit_one)(spec, quadratic_a, quadratic_c) for spec in ordered_specs
    )
    frame = pd.DataFrame(rows).sort_values(["topology", "p", "seed"])
    frame.to_csv(ROOT / args.csv, index=False)

    by_topology = (
        frame.groupby("topology")
        .agg(
            graphs=("seed", "size"),
            depth_ok=("oracle_search_depth_premise_satisfied", "sum"),
            certified_depth_failures=("oracle_depth_audit_mode", _count_depth_failures),
            min_complete_edge_margin=("oracle_edge_partial_corr_min", "min"),
            min_selected_edge_margin=("selected_edge_partial_corr_min", "min"),
            min_selected_edge_query_retention=("selected_edge_query_retention_min", "min"),
        )
        .reset_index()
    )

    query_audited = frame[
        frame["oracle_pc_query_diagnostics_run"].fillna(False).astype(bool)
    ]
    covered = frame[
        frame["oracle_search_depth_premise_satisfied"].fillna(False).astype(bool)
    ]
    stress = frame[
        ~frame["oracle_search_depth_premise_satisfied"].fillna(False).astype(bool)
    ]

    report = {
        "unique_graph_structures": int(len(frame)),
        "depth_premise_satisfied": int(len(covered)),
        "depth_premise_stress": int(len(stress)),
        "certified_failure_witnesses": int(
            (stress["oracle_depth_audit_mode"].astype(str) == "early_exit_failure_witness").sum()
        ),
        "all_depth_covered_are_exhaustive_passes": bool(
            (covered["oracle_depth_audit_mode"].astype(str) == "exhaustive_pass").all()
        ),
        "stress_coverage_fraction_intentionally_unreported": bool(
            stress["oracle_separator_coverage_fraction"].isna().all()
        ),
        "exact_oracle_query_audits": int(len(query_audited)),
        "exact_oracle_null_numeric_all": (
            bool(query_audited["oracle_pc_null_numeric_check"].fillna(False).astype(bool).all())
            if len(query_audited)
            else None
        ),
        "exact_selected_oracle_null_numeric_all": (
            bool(
                query_audited["selected_oracle_pc_null_numeric_check"]
                .fillna(False)
                .astype(bool)
                .all()
            )
            if len(query_audited)
            else None
        ),
        "exact_oracle_skeleton_all": (
            bool(query_audited["oracle_pc_exact_skeleton"].fillna(False).astype(bool).all())
            if len(query_audited)
            else None
        ),
        "min_depth_covered_complete_edge_margin": (
            float(covered["oracle_edge_partial_corr_min"].min()) if len(covered) else None
        ),
        "min_depth_covered_selected_edge_margin": (
            float(covered["selected_edge_partial_corr_min"].min()) if len(covered) else None
        ),
        "min_depth_covered_selected_edge_query_retention": (
            float(covered["selected_edge_query_retention_min"].min())
            if len(covered)
            else None
        ),
        "min_exact_complete_dependent_query_margin": (
            float(query_audited["oracle_pc_dependent_partial_corr_min"].min())
            if len(query_audited)
            else None
        ),
        "min_exact_selected_dependent_query_margin": (
            float(query_audited["selected_oracle_pc_dependent_partial_corr_min"].min())
            if len(query_audited)
            else None
        ),
        "min_exact_selected_oracle_query_retention": (
            float(query_audited["selected_oracle_pc_query_retention_min"].min())
            if len(query_audited)
            else None
        ),
        "by_topology": by_topology.to_dict(orient="records"),
        "interpretation": (
            "Depth status is exact: a passing graph is exhaustively checked over every "
            "nonedge; a failing graph carries a concrete nonedge with no true-adjacency "
            "separator through d_alg and exits early. Coverage fractions are intentionally "
            "NaN on failed graphs because no exhaustive fraction is needed. Population "
            "margins are finite-grid diagnostics, not a proof of a dimension-uniform "
            "strong-faithfulness constant. Selected-law diagnostics apply only to "
            "depth-covered Gaussian-preserving quadratic cells; logistic masking remains "
            "a distributional stress regime."
        ),
    }
    (ROOT / args.json).write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    print(json.dumps(report, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
