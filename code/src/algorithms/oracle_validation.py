"""Oracle validation helpers for skeleton-search logic.

This module uses exact d-separation in a known DAG.  It is not an estimator for
observed data.  Its role is to validate search logic independently of sampling
noise, missingness, and CI-test calibration.

Two target procedures are deliberately distinguished:

``target_pc_simple_oracle``
    Mirrors the repository's candidate-pruning target-only heuristic.  It
    conditions only on the target's current candidate set.  This procedure is
    computationally attractive but is not skeleton-sound for arbitrary faithful
    DAGs.

``target_bounded_separator_oracle``
    For every candidate X, searches all subsets of V\\{T,X} up to a specified
    size.  With an oracle CI test, it is sound whenever every non-neighbour has a
    separating set no larger than the configured bound.  It is expensive and is
    included as a correctness benchmark rather than a default scalable method.
"""
from __future__ import annotations

from itertools import combinations
from typing import Iterable, Iterator, Sequence, Set, Tuple

import networkx as nx


def skeleton_edge_set(graph: nx.DiGraph | nx.Graph) -> set[frozenset[str]]:
    """Return the undirected edge set with string-normalized node labels."""
    return {
        frozenset((str(u), str(v)))
        for u, v in graph.edges()
        if str(u) != str(v)
    }


def is_d_separated(
    dag: nx.DiGraph,
    x: str,
    y: str,
    conditioning_set: Iterable[str],
) -> bool:
    """Exact oracle CI decision through NetworkX d-separation."""
    return bool(nx.is_d_separator(dag, {x}, {y}, set(conditioning_set)))


def global_pc_stable_oracle(
    dag: nx.DiGraph,
    max_conditioning_set_size: int | None = None,
) -> nx.Graph:
    """Mirror the repository's two-sided PC-stable skeleton search with an oracle."""
    variables = sorted(map(str, dag.nodes()))
    max_size = len(variables) - 2 if max_conditioning_set_size is None else int(max_conditioning_set_size)
    graph = nx.Graph()
    graph.add_nodes_from(variables)
    graph.add_edges_from(combinations(variables, 2))

    for level in range(max_size + 1):
        adjacency_snapshot = {node: set(graph.neighbors(node)) for node in variables}
        any_testable_edge = False
        for x, y in sorted(graph.edges()):
            if not graph.has_edge(x, y):
                continue
            adj_x = adjacency_snapshot[x] - {y}
            adj_y = adjacency_snapshot[y] - {x}
            if max(len(adj_x), len(adj_y)) < level:
                continue
            any_testable_edge = True
            candidates = sorted({
                tuple(cond)
                for pool in (adj_x, adj_y)
                if len(pool) >= level
                for cond in combinations(tuple(sorted(pool)), level)
            })
            for cond in candidates:
                if is_d_separated(dag, x, y, cond):
                    graph.remove_edge(x, y)
                    break
        if not any_testable_edge:
            break
    return graph


def target_pc_simple_oracle(
    dag: nx.DiGraph,
    target: str,
    max_conditioning_set_size: int | None = None,
) -> set[str]:
    """Mirror the repository's current target-only candidate-pruning heuristic."""
    variables = sorted(map(str, dag.nodes()))
    if target not in variables:
        raise ValueError(f"Unknown target {target!r}")
    max_size = len(variables) - 2 if max_conditioning_set_size is None else int(max_conditioning_set_size)
    neighbors: Set[str] = {v for v in variables if v != target}

    for size in range(max_size + 1):
        snapshot = set(neighbors)
        any_testable_candidate = False
        for x in sorted(snapshot):
            if x not in neighbors:
                continue
            candidate_z = snapshot - {x}
            if len(candidate_z) < size:
                continue
            any_testable_candidate = True
            for cond in combinations(tuple(sorted(candidate_z)), size):
                if is_d_separated(dag, target, x, cond):
                    neighbors.discard(x)
                    break
        if not any_testable_candidate:
            break
    return neighbors


def target_bounded_separator_oracle(
    dag: nx.DiGraph,
    target: str,
    max_conditioning_set_size: int | None = None,
) -> set[str]:
    """Target skeleton search over all bounded-size separators.

    A candidate is removed if any subset of all remaining observed variables,
    not merely the target's current candidate set, d-separates it from the
    target.  This is a correctness benchmark for bounded separator size.
    """
    variables = sorted(map(str, dag.nodes()))
    if target not in variables:
        raise ValueError(f"Unknown target {target!r}")
    max_size = len(variables) - 2 if max_conditioning_set_size is None else int(max_conditioning_set_size)
    retained: set[str] = set()
    for x in variables:
        if x == target:
            continue
        pool = [v for v in variables if v not in {target, x}]
        separated = False
        for size in range(min(max_size, len(pool)) + 1):
            for cond in combinations(pool, size):
                if is_d_separated(dag, target, x, cond):
                    separated = True
                    break
            if separated:
                break
        if not separated:
            retained.add(x)
    return retained


def ordered_dags(n_nodes: int) -> Iterator[nx.DiGraph]:
    """Enumerate every DAG compatible with one fixed topological order.

    This gives ``2^(n choose 2)`` labeled DAGs.  It is sufficient for systematic
    small-graph search-logic testing while remaining tractable through n=5.
    """
    if n_nodes < 1:
        raise ValueError("n_nodes must be positive")
    nodes = [f"X{i}" for i in range(n_nodes)]
    possible_edges = list(combinations(nodes, 2))
    for bits in range(1 << len(possible_edges)):
        dag = nx.DiGraph()
        dag.add_nodes_from(nodes)
        for index, edge in enumerate(possible_edges):
            if (bits >> index) & 1:
                dag.add_edge(*edge)
        yield dag


def true_target_neighbors(dag: nx.DiGraph, target: str) -> set[str]:
    """Return the true undirected neighbors of a target node in the ground-truth DAG."""
    return set(map(str, dag.to_undirected().neighbors(target)))
