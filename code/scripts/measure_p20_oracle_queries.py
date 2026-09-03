#!/usr/bin/env python3
"""Audit exact bounded-depth oracle-PC queries on the registered p=20 structures.

This finite-grid diagnostic evaluates the exact oracle search path under the
complete Gaussian law and the Gaussian-preserving quadratic selected law. It is
not a dimension-uniform strong-faithfulness statement and does not validate the
finite-sample CI test by itself.
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
    linear_sem_covariance,
    oracle_pc_query_margin_diagnostics,
    pc_separator_depth_diagnostics,
)


def _unique_p20_specs(config: dict) -> dict[tuple, dict]:
    """Return one specification per unique p=20 graph/SEM structure."""
    unique: dict[tuple, dict] = {}
    for spec in expand_specs(config, quick=False):
        if int(spec["p"]) != 20:
            continue
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
        "seed": seed,
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
    row.update(
        oracle_pc_query_margin_diagnostics(
            graph,
            covariance,
            nodes,
            depth,
            selected_quadratic_masked_nodes=set(nodes),
            selected_quadratic_a=quadratic_a,
            selected_quadratic_c=quadratic_c,
        )
    )
    return row


def main() -> int:
    """Measure exact p=20 oracle-query margins on the registered primary structures."""
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--config", default="configs/primary_scaling.yaml")
    parser.add_argument("--csv", default="p20_oracle_queries.csv")
    parser.add_argument("--json", default="p20_oracle_queries.json")
    parser.add_argument("--n-jobs", type=int, default=8)
    args = parser.parse_args()

    config = yaml.safe_load((ROOT / args.config).read_text())
    unique = _unique_p20_specs(config)

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
    frame = pd.DataFrame(rows).sort_values(["topology", "seed"])
    frame.to_csv(ROOT / args.csv, index=False)

    covered = frame[frame["depth_ok"]].copy()
    by_topology = []
    for topology, group in covered.groupby("topology", sort=True):
        by_topology.append(
            {
                "topology": str(topology),
                "graphs": int(len(group)),
                "min_dep": float(group["oracle_pc_dependent_partial_corr_min"].min()),
                "min_sel_dep": float(
                    group["selected_oracle_pc_dependent_partial_corr_min"].min()
                ),
                "min_ret": float(group["selected_oracle_pc_query_retention_min"].min()),
            }
        )

    report = {
        "graphs": int(len(frame)),
        "depth_covered": int(len(covered)),
        "oracle_exact_all": bool(covered["oracle_pc_exact_skeleton"].eq(True).all()),
        "null_numeric_all": bool(covered["oracle_pc_null_numeric_check"].eq(True).all()),
        "selected_null_numeric_all": bool(
            covered["selected_oracle_pc_null_numeric_check"].eq(True).all()
        ),
        "min_dependent_margin": float(covered["oracle_pc_dependent_partial_corr_min"].min()),
        "min_selected_dependent_margin": float(
            covered["selected_oracle_pc_dependent_partial_corr_min"].min()
        ),
        "min_selected_query_retention": float(
            covered["selected_oracle_pc_query_retention_min"].min()
        ),
        "by_topology": by_topology,
        "interpretation": (
            "Finite p=20 exact oracle-path audit only. Exact recovery verifies the "
            "registered bounded-depth oracle path on these structures; it does not "
            "imply a dimension-uniform margin or validate the practical finite-sample "
            "CI test on its own."
        ),
    }
    (ROOT / args.json).write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
