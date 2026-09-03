#!/usr/bin/env python3
"""Audit the bounded-depth search premise on every unique registered graph.

For each true nonedge, this diagnostic asks whether a true-adjacency separator
of size at most ``d_alg`` exists. Passing graphs are exhaustively certified;
failing graphs return a concrete witness and stop early. Population-margin
calculations are intentionally outside this script.
"""
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

import pandas as pd
import yaml
from joblib import Parallel, delayed

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "code"))

from experiments.run_recovery_experiments import expand_specs, topology_spec
from src.data_generation.linear_gaussian_sem import generate_graph
from src.data_generation.sem_diagnostics import pc_separator_depth_diagnostics


def _unique_specs(config: dict) -> dict[tuple, dict]:
    unique: dict[tuple, dict] = {}
    for spec in expand_specs(config, quick=False):
        key = (
            str(spec["topology_name"]),
            int(spec["p"]),
            int(spec["seed"]),
            int(spec["max_conditioning_set_size"]),
        )
        unique.setdefault(key, spec)
    return unique


def _audit_one(spec: dict) -> dict:
    p = int(spec["p"])
    depth = int(spec["max_conditioning_set_size"])
    seed = int(spec["seed"])
    topology, params = topology_spec(spec["topology_entry"], p)
    graph = generate_graph(topology, p, params, seed)
    return {
        "topology": str(spec["topology_name"]),
        "p": p,
        "seed": seed,
        "d_alg": depth,
        "true_edges": int(graph.number_of_edges()),
        **pc_separator_depth_diagnostics(graph, depth),
    }


def _count_certified_failures(values: pd.Series) -> int:
    return int((values.astype(str) == "early_exit_failure_witness").sum())


def main() -> int:
    """Measure bounded-depth separator coverage on the registered primary structures."""
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--config", default="configs/primary_scaling.yaml")
    parser.add_argument("--csv", default="depth_scope.csv")
    parser.add_argument("--json", default="depth_scope.json")
    parser.add_argument("--n-jobs", type=int, default=8)
    args = parser.parse_args()

    config = yaml.safe_load((ROOT / args.config).read_text())
    unique = _unique_specs(config)
    rows = Parallel(n_jobs=int(args.n_jobs), prefer="processes")(
        delayed(_audit_one)(spec) for _, spec in sorted(unique.items())
    )
    frame = pd.DataFrame(rows).sort_values(["topology", "p", "seed"])
    (ROOT / args.csv).write_text(frame.to_csv(index=False))

    by_topology_p = (
        frame.groupby(["topology", "p"])
        .agg(
            graphs=("seed", "size"),
            depth_ok=("oracle_search_depth_premise_satisfied", "sum"),
            certified_failures=("oracle_depth_audit_mode", _count_certified_failures),
        )
        .reset_index()
    )
    by_topology = (
        frame.groupby("topology")
        .agg(
            graphs=("seed", "size"),
            depth_ok=("oracle_search_depth_premise_satisfied", "sum"),
            certified_failures=("oracle_depth_audit_mode", _count_certified_failures),
        )
        .reset_index()
    )

    report = {
        "unique_graph_structures": int(len(frame)),
        "depth_premise_satisfied": int(
            frame["oracle_search_depth_premise_satisfied"].sum()
        ),
        "depth_premise_stress": int(
            (~frame["oracle_search_depth_premise_satisfied"].astype(bool)).sum()
        ),
        "by_topology": by_topology.to_dict(orient="records"),
        "by_topology_p": by_topology_p.to_dict(orient="records"),
        "interpretation": (
            "Passing graphs are exhaustively certified for the registered d_alg. "
            "Failing graphs carry a concrete nonedge witness with no true-adjacency "
            "separator through d_alg; failure rows are stress regimes, not "
            "bounded-depth oracle-search instantiations."
        ),
    }
    (ROOT / args.json).write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    print(json.dumps(report, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
