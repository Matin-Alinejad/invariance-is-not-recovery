"""Dedicated theorem-aligned linear-Gaussian SEM generator for registered recovery evidence.

Design invariants
-----------------
1. Graph generation depends on ``(topology, p, seed)`` only.
2. Structural coefficients depend on ``(graph, seed, signal_range)`` only — never ``n``.
3. Row-noise draws use a separate deterministic RNG stream. For fixed
   ``(graph, seed)`` and two sample sizes, the smaller dataset is exactly the
   row-prefix of the larger dataset.
4. No sample-fitted standardization is applied.
5. Innovations are iid N(0,1), matching ``linear_sem_covariance`` exactly.

These properties are deliberately stricter than the repository's general
synthetic-data factory because the registered scaling experiment needs
matched SEMs across sample-size schedules and fixed population-calibrated
self-masking.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Mapping

import networkx as nx
import numpy as np
import pandas as pd

from .synthetic_graphs import GraphTopology, GraphTopologyGenerator


@dataclass(frozen=True)
class LinearGaussianSample:
    """Generated data, ground-truth DAG, and realized SEM parameters for one cell."""
    data: pd.DataFrame
    ground_truth_graph: nx.DiGraph
    causal_parameters: dict[str, Any]


def generate_graph(
    topology: GraphTopology,
    n_variables: int,
    topology_params: Mapping[str, Any],
    seed: int,
) -> nx.DiGraph:
    """Generate exactly one DAG without touching the SEM/noise RNG streams."""
    p = int(n_variables)
    params = dict(topology_params)
    if topology == GraphTopology.CHAIN:
        return GraphTopologyGenerator.generate_chain(p, seed)
    if topology == GraphTopology.FORK:
        return GraphTopologyGenerator.generate_fork(p, seed)
    if topology == GraphTopology.COLLIDER:
        return GraphTopologyGenerator.generate_collider(p, seed)
    if topology == GraphTopology.RANDOM:
        return GraphTopologyGenerator.generate_random(p, float(params.get("edge_prob", 0.3)), seed)
    if topology == GraphTopology.RANDOM_REGULAR:
        return GraphTopologyGenerator.generate_random_regular(p, int(params.get("degree", 2)), seed)
    if topology == GraphTopology.SCALE_FREE:
        return GraphTopologyGenerator.generate_scale_free(p, int(params.get("m", 2)), seed)
    if topology == GraphTopology.SMALL_WORLD:
        return GraphTopologyGenerator.generate_small_world(
            p, int(params.get("k", 2)), float(params.get("p", 0.1)), seed
        )
    if topology == GraphTopology.MIXED:
        return GraphTopologyGenerator.generate_mixed(p, seed)
    if topology == GraphTopology.FIXED:
        return GraphTopologyGenerator.generate_fixed(
            p,
            list(params.get("node_names", [])),
            list(params.get("edges", [])),
            seed,
        )
    raise ValueError(f"Unsupported registered graph topology: {topology}")


def _rng(seed: int, stream: int) -> np.random.Generator:
    # SeedSequence with separate stream labels gives deterministic independent
    # pseudorandom streams without dependence on how many draws another stream uses.
    return np.random.default_rng(np.random.SeedSequence([int(seed), int(stream)]))


def generate_linear_gaussian_sample(
    *,
    graph: nx.DiGraph,
    n_samples: int,
    seed: int,
    signal_low: float,
    signal_high: float,
) -> LinearGaussianSample:
    """Simulate iid rows from a fixed sparse linear-Gaussian SEM.

    Coefficients are sampled from a structural-parameter stream independent of
    ``n_samples``. Noise is drawn as an ``(n,p)`` matrix from another stream so
    changing ``n`` preserves the row-prefix coupling.
    """
    n = int(n_samples)
    low, high = float(signal_low), float(signal_high)
    if n <= 0:
        raise ValueError("n_samples must be positive")
    if not (0.0 <= low <= high):
        raise ValueError("signal range must satisfy 0 <= low <= high")
    if not nx.is_directed_acyclic_graph(graph):
        raise ValueError("linear-Gaussian generator requires a DAG")

    nodes = list(map(str, graph.nodes()))
    index = {node: i for i, node in enumerate(nodes)}
    topo_order = list(map(str, nx.topological_sort(graph)))

    param_rng = _rng(seed, 0x53545255)  # "STRU"
    noise_rng = _rng(seed, 0x4E4F4953)  # "NOIS"

    # Fix all structural parameters before any row-noise draw.
    weights_by_node: dict[str, tuple[list[str], np.ndarray]] = {}
    causal_parameters: dict[str, Any] = {}
    for node in topo_order:
        parents = sorted(map(str, graph.predecessors(node)))
        if not parents:
            continue
        magnitudes = param_rng.uniform(low, high, len(parents))
        signs = param_rng.choice(np.array([-1.0, 1.0]), size=len(parents))
        weights = np.asarray(signs * magnitudes, dtype=float)
        weights_by_node[node] = (parents, weights)
        causal_parameters[node] = {
            "parents": parents,
            "causal_function": "linear",
            "parameters": {
                "weights": weights.tolist(),
                "min_abs_weight_configured": low,
                "max_abs_weight_configured": high,
            },
            "noise_distribution": "gaussian",
            "noise_params": {"mean": 0.0, "std": 1.0},
        }

    noise = noise_rng.normal(0.0, 1.0, size=(n, len(nodes)))
    data = np.zeros_like(noise)
    for node in topo_order:
        j = index[node]
        if node not in weights_by_node:
            data[:, j] = noise[:, j]
            continue
        parents, weights = weights_by_node[node]
        parent_idx = [index[parent] for parent in parents]
        data[:, j] = data[:, parent_idx] @ weights + noise[:, j]

    return LinearGaussianSample(
        data=pd.DataFrame(data, columns=nodes),
        ground_truth_graph=graph.copy(),
        causal_parameters=causal_parameters,
    )
