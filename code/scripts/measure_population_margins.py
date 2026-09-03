#!/usr/bin/env python3
"""Measure population CI margins and query retention on depth-covered structures.

This finite-grid diagnostic records the realized minimum nonzero edge-query
partial correlations and quadratic-selected query-retention values for the
registered SEMs whose bounded-depth search premise holds. It does not establish
a dimension-uniform strong-faithfulness constant.
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
    pc_separator_depth_diagnostics,
    quadratic_selected_edge_query_diagnostics,
)


def _unique_specs(config: dict) -> dict[tuple, dict]:
    """Return one specification per unique graph/SEM/depth combination."""
    unique: dict[tuple, dict] = {}
    for spec in expand_specs(config, quick=False):
        key = (
            str(spec["topology_name"]),
            int(spec["p"]),
            int(spec["seed"]),
            float(spec["signal_low"]),
            float(spec["signal_high"]),
            int(spec["max_conditioning_set_size"]),
        )
        unique.setdefault(key, spec)
    return unique


def _audit_one(spec: dict, quadratic_a: float, quadratic_c: float) -> dict:
    p = int(spec["p"])
    seed = int(spec["seed"])
    depth = int(spec["max_conditioning_set_size"])
    topology, params = topology_spec(spec["topology_entry"], p)
    graph = generate_graph(topology, p, params, seed)
    depth_report = pc_separator_depth_diagnostics(graph, depth)

    row = {
        "topology": str(spec["topology_name"]),
        "p": p,
        "seed": seed,
        "d_alg": depth,
        "depth_ok": bool(depth_report["oracle_search_depth_premise_satisfied"]),
    }
    if not row["depth_ok"]:
        return row

    generated = generate_linear_gaussian_sample(
        graph=graph,
        n_samples=2,
        seed=seed,
        signal_low=float(spec["signal_low"]),
        signal_high=float(spec["signal_high"]),
    )
    nodes, covariance = linear_sem_covariance(graph, generated.causal_parameters)
    row.update(edge_partial_correlation_margin(graph, covariance, nodes, depth))
    row.update(
        quadratic_selected_edge_query_diagnostics(
            graph,
            covariance,
            nodes,
            depth,
            masked_nodes=set(nodes),
            quadratic_a=quadratic_a,
            quadratic_c=quadratic_c,
        )
    )
    return row


def main() -> int:
    """Measure population partial-correlation margins and selected-query retention diagnostics."""
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--config", default="configs/primary_scaling.yaml")
    parser.add_argument("--csv", default="population_margins.csv")
    parser.add_argument("--json", default="population_margins.json")
    parser.add_argument("--n-jobs", type=int, default=8)
    args = parser.parse_args()

    config = yaml.safe_load((ROOT / args.config).read_text())
    unique = _unique_specs(config)

    target_missing_rate = 0.30
    target_retention = 1.0 - target_missing_rate
    quadratic_a = choose_quadratic_a(
        target_retention,
        float(config["base"].get("quadratic_a", 0.2)),
    )
    quadratic_c = target_retention * np.sqrt(1.0 + quadratic_a)

    rows = Parallel(n_jobs=args.n_jobs, prefer="processes")(
        delayed(_audit_one)(spec, quadratic_a, quadratic_c)
        for _, spec in sorted(unique.items())
    )
    frame = pd.DataFrame(rows).sort_values(["topology", "p", "seed"])
    frame.to_csv(ROOT / args.csv, index=False)

    covered = frame[frame["depth_ok"]].copy()
    by_topology = (
        covered.groupby("topology")
        .agg(
            graphs=("seed", "size"),
            min_complete_edge_margin=("oracle_edge_partial_corr_min", "min"),
            min_selected_edge_margin=("selected_edge_partial_corr_min", "min"),
            min_selected_query_retention=("selected_edge_query_retention_min", "min"),
            q10_selected_query_retention=(
                "selected_edge_query_retention_min",
                lambda values: float(np.quantile(values.dropna(), 0.1)),
            ),
        )
        .reset_index()
    )

    report = {
        "registered_graphs": int(len(frame)),
        "depth_covered_graphs": int(len(covered)),
        "quadratic_a": float(quadratic_a),
        "quadratic_c": float(quadratic_c),
        "min_complete_edge_margin": float(covered["oracle_edge_partial_corr_min"].min()),
        "min_selected_edge_margin": float(covered["selected_edge_partial_corr_min"].min()),
        "min_selected_query_retention": float(
            covered["selected_edge_query_retention_min"].min()
        ),
        "by_topology": by_topology.to_dict(orient="records"),
        "interpretation": (
            "These are finite registered-grid diagnostics only. They support checking "
            "the premises of the explicit finite-sample corollary but are not evidence "
            "of a p-uniform strong-faithfulness constant beyond the registered family."
        ),
    }
    (ROOT / args.json).write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    print(json.dumps(report, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
