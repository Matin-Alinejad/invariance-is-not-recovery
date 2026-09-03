"""Randomized exact d-separation stress audit for skeleton-search procedures."""
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any, Dict, List

import networkx as nx
import numpy as np

REPO_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO_ROOT / "code"))

from src.algorithms.oracle_validation import (
    global_pc_stable_oracle,
    skeleton_edge_set,
    target_bounded_separator_oracle,
    target_pc_simple_oracle,
    true_target_neighbors,
)
from src.data_generation.sem_diagnostics import pc_separator_depth_diagnostics


def random_ordered_dag(p: int, average_degree: float, rng: np.random.Generator) -> nx.DiGraph:
    """Generate a deterministic random ordered DAG for oracle-search stress testing."""
    nodes = [f"X{i}" for i in range(p)]
    order = list(rng.permutation(nodes))
    edge_probability = min(1.0, max(0.0, float(average_degree) / max(1, p - 1)))
    dag = nx.DiGraph()
    dag.add_nodes_from(nodes)
    for i in range(p):
        for j in range(i + 1, p):
            if rng.random() < edge_probability:
                dag.add_edge(order[i], order[j])
    return dag


def audit(
    node_sizes: List[int],
    graphs_per_size: int = 25,
    average_degree: float = 2.0,
    seed: int = 20260724,
) -> Dict[str, Any]:
    """Compare bounded oracle search against exact d-separation over randomized DAG queries."""
    if not node_sizes or any(p < 2 or p > 12 for p in node_sizes):
        raise ValueError("node_sizes must lie in [2,12]")
    if graphs_per_size <= 0:
        raise ValueError("graphs_per_size must be positive")
    rng = np.random.default_rng(seed)
    summaries = []
    counterexamples = []
    for p in node_sizes:
        global_failures = 0
        bounded_failures = 0
        heuristic_failures = 0
        target_cases = 0
        depth_failures = 0
        edge_counts = []
        max_degrees = []
        for graph_index in range(graphs_per_size):
            dag = random_ordered_dag(p, average_degree, rng)
            edge_counts.append(dag.number_of_edges())
            max_degrees.append(max(dict(dag.to_undirected().degree()).values(), default=0))
            full_depth = p - 2
            depth = pc_separator_depth_diagnostics(dag, full_depth)
            if not depth["oracle_search_depth_premise_satisfied"]:
                depth_failures += 1
            global_estimate = global_pc_stable_oracle(dag, full_depth)
            if skeleton_edge_set(global_estimate) != skeleton_edge_set(dag):
                global_failures += 1
                if len(counterexamples) < 10:
                    counterexamples.append({
                        "procedure": "global_pc_stable",
                        "p": p,
                        "graph_index": graph_index,
                        "dag_edges": sorted([list(edge) for edge in dag.edges()]),
                        "estimate_edges": sorted([sorted(edge) for edge in skeleton_edge_set(global_estimate)]),
                    })
            for target in sorted(map(str, dag.nodes())):
                target_cases += 1
                truth = true_target_neighbors(dag, target)
                bounded = target_bounded_separator_oracle(dag, target, full_depth)
                heuristic = target_pc_simple_oracle(dag, target, full_depth)
                if bounded != truth:
                    bounded_failures += 1
                    if len(counterexamples) < 10:
                        counterexamples.append({
                            "procedure": "target_bounded_separator",
                            "p": p,
                            "graph_index": graph_index,
                            "target": target,
                            "dag_edges": sorted([list(edge) for edge in dag.edges()]),
                            "truth": sorted(truth),
                            "estimate": sorted(bounded),
                        })
                if heuristic != truth:
                    heuristic_failures += 1
        summaries.append({
            "p": p,
            "graphs": graphs_per_size,
            "target_cases": target_cases,
            "mean_edges": float(np.mean(edge_counts)),
            "max_realized_degree": int(max(max_degrees, default=0)),
            "full_depth_separator_premise_failures": depth_failures,
            "global_pc_stable_failures": global_failures,
            "target_bounded_separator_failures": bounded_failures,
            "target_pc_simple_failures": heuristic_failures,
        })
    return {
        "node_sizes": node_sizes,
        "graphs_per_size": graphs_per_size,
        "average_degree_target": average_degree,
        "seed": seed,
        "summaries": summaries,
        "first_counterexamples": counterexamples,
        "interpretation": (
            "This randomized audit complements, but does not replace, exhaustive small-DAG "
            "enumeration. Zero failures for an oracle procedure are implementation evidence, "
            "not a theorem. PC-simple failures are expected because that heuristic is not "
            "generally skeleton-sound."
        ),
    }


def main() -> None:
    """Run the randomized oracle-search stress audit and write its report."""
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--node-sizes", nargs="+", type=int, default=[6, 8, 10])
    parser.add_argument("--graphs-per-size", type=int, default=25)
    parser.add_argument("--average-degree", type=float, default=2.0)
    parser.add_argument("--seed", type=int, default=20260724)
    parser.add_argument("--output", default=str(REPO_ROOT / "oracle_search_stress_test.json"))
    args = parser.parse_args()
    result = audit(args.node_sizes, args.graphs_per_size, args.average_degree, args.seed)
    output = Path(args.output)
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
