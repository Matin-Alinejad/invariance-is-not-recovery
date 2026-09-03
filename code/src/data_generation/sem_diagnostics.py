"""Population diagnostics for linear-Gaussian SEM experiments."""
from __future__ import annotations

from itertools import combinations
from typing import Any, Mapping

import networkx as nx
import numpy as np


def linear_sem_covariance(
    graph: nx.DiGraph,
    causal_parameters: Mapping[str, Any],
    *,
    noise_variance: float = 1.0,
) -> tuple[list[str], np.ndarray]:
    """Reconstruct the population covariance from the generated linear SEM.

    The generator stores, for each non-root node, its ordered parent list and the
    corresponding coefficient vector.  With ``X = A X + eps``, the covariance is
    ``(I-A)^-1 Omega (I-A)^-T``.
    """
    if noise_variance <= 0:
        raise ValueError("noise_variance must be positive")
    nodes = list(map(str, graph.nodes()))
    index = {node: i for i, node in enumerate(nodes)}
    a = np.zeros((len(nodes), len(nodes)), dtype=float)
    for child, info in causal_parameters.items():
        child = str(child)
        if child not in index:
            raise KeyError(f"Unknown child in causal parameters: {child}")
        parents = list(map(str, info.get("parents", [])))
        weights = list(info.get("parameters", {}).get("weights", []))
        if len(parents) != len(weights):
            raise ValueError(f"Parent/weight mismatch for {child}: {len(parents)} vs {len(weights)}")
        for parent, weight in zip(parents, weights):
            a[index[child], index[parent]] = float(weight)
    transform = np.linalg.inv(np.eye(len(nodes)) - a)
    covariance = transform @ (noise_variance * np.eye(len(nodes))) @ transform.T
    covariance = (covariance + covariance.T) / 2.0
    eig_min = float(np.linalg.eigvalsh(covariance).min())
    if eig_min <= 0:
        raise ValueError(f"Reconstructed covariance is not positive definite; min eigenvalue={eig_min}")
    return nodes, covariance


def partial_correlation_from_covariance(
    covariance: np.ndarray,
    i: int,
    j: int,
    conditioning: list[int] | tuple[int, ...],
) -> float:
    """Population partial correlation from a positive-definite covariance."""
    selected = [int(i), int(j), *map(int, conditioning)]
    sub = np.asarray(covariance, dtype=float)[np.ix_(selected, selected)]
    precision = np.linalg.inv(sub)
    denom = float(np.sqrt(precision[0, 0] * precision[1, 1]))
    if not np.isfinite(denom) or denom <= 0:
        return np.nan
    value = float(-precision[0, 1] / denom)
    return float(np.clip(value, -1.0, 1.0))


def edge_partial_correlation_margin(
    graph: nx.DiGraph,
    covariance: np.ndarray,
    nodes: list[str],
    max_conditioning_set_size: int,
) -> dict[str, float | int | bool]:
    """Audit true-edge partial correlations over PC-style local conditioning pools.

    This is a diagnostic, not a proof of global strong faithfulness.  For each
    true skeleton edge, it checks all subsets up to the configured depth from
    either endpoint's *true* adjacency set.
    """
    if max_conditioning_set_size < 0:
        raise ValueError("max_conditioning_set_size must be nonnegative")
    index = {node: i for i, node in enumerate(nodes)}
    skeleton = graph.to_undirected()
    values: list[float] = []
    for u, v in sorted((str(u), str(v)) for u, v in skeleton.edges()):
        pools = (set(map(str, skeleton.neighbors(u))) - {v},
                 set(map(str, skeleton.neighbors(v))) - {u})
        conditioning_sets = {()}
        for pool in pools:
            ordered = tuple(sorted(pool))
            for size in range(1, min(max_conditioning_set_size, len(ordered)) + 1):
                conditioning_sets.update(combinations(ordered, size))
        for cond in sorted(conditioning_sets):
            rho = partial_correlation_from_covariance(
                covariance, index[u], index[v], [index[x] for x in cond]
            )
            if np.isfinite(rho):
                values.append(abs(float(rho)))
    arr = np.asarray(values, dtype=float)
    if not len(arr):
        return {
            "oracle_edge_query_count": 0,
            "oracle_edge_partial_corr_min": np.nan,
            "oracle_edge_partial_corr_q10": np.nan,
            "oracle_edge_partial_corr_median": np.nan,
            "oracle_edge_partial_corr_below_001": 0,
            "oracle_edge_partial_corr_below_005": 0,
            "oracle_edge_partial_corr_below_010": 0,
            "oracle_edge_margin_finite": False,
        }
    return {
        "oracle_edge_query_count": int(len(arr)),
        "oracle_edge_partial_corr_min": float(arr.min()),
        "oracle_edge_partial_corr_q10": float(np.quantile(arr, 0.10)),
        "oracle_edge_partial_corr_median": float(np.median(arr)),
        "oracle_edge_partial_corr_below_001": int(np.sum(arr < 0.01)),
        "oracle_edge_partial_corr_below_005": int(np.sum(arr < 0.05)),
        "oracle_edge_partial_corr_below_010": int(np.sum(arr < 0.10)),
        "oracle_edge_margin_finite": bool(np.all(np.isfinite(arr))),
    }



def quadratic_selected_query_stats(
    covariance: np.ndarray,
    query_indices: list[int] | tuple[int, ...],
    *,
    population_variances: np.ndarray,
    masked_indices: set[int],
    quadratic_a: float,
    quadratic_c: float,
) -> tuple[float, float]:
    """Selected-law partial correlation and exact query retention.

    For the centered quadratic mask used in the registered experiment, each masked
    coordinate ``k`` is retained with
    ``c exp[-a X_k^2/(2 Var(X_k))]``.  On a Gaussian query subvector this is a
    diagonal Gaussian tilt.  The selected precision is therefore
    ``Sigma_Q^{-1} + D_Q`` and the query-retention probability is the Gaussian
    quadratic-form integral
    ``c^m / sqrt(det(I + Sigma_Q D_Q))``.

    This helper is diagnostic only; it does not replace the hand proof or the
    formal recovery argument.
    """
    idx=[int(i) for i in query_indices]
    if len(idx)<2:
        raise ValueError('query must contain at least the tested pair')
    if quadratic_a < 0 or not (0 < quadratic_c <= 1):
        raise ValueError('invalid quadratic-mask parameters')
    sub=np.asarray(covariance,dtype=float)[np.ix_(idx,idx)]
    precision=np.linalg.inv(sub)
    diag=np.zeros(len(idx),dtype=float)
    masked_count=0
    for pos,ambient in enumerate(idx):
        if ambient in masked_indices:
            var=float(population_variances[ambient])
            if not np.isfinite(var) or var<=0:
                raise ValueError(f'bad population variance at index {ambient}: {var}')
            diag[pos]=float(quadratic_a)/var
            masked_count += 1
    selected_precision=precision+np.diag(diag)
    denom=float(np.sqrt(selected_precision[0,0]*selected_precision[1,1]))
    rho=float(-selected_precision[0,1]/denom) if np.isfinite(denom) and denom>0 else np.nan
    # det(I + Sigma D) is strictly positive for Sigma PD and D PSD.
    sign,logdet=np.linalg.slogdet(np.eye(len(idx))+sub@np.diag(diag))
    if sign<=0 or not np.isfinite(logdet):
        retention=np.nan
    else:
        retention=float((quadratic_c**masked_count)*np.exp(-0.5*logdet))
    return float(np.clip(rho,-1.0,1.0)) if np.isfinite(rho) else np.nan, retention


def quadratic_selected_edge_query_diagnostics(
    graph: nx.DiGraph,
    covariance: np.ndarray,
    nodes: list[str],
    max_conditioning_set_size: int,
    *,
    masked_nodes: set[str],
    quadratic_a: float,
    quadratic_c: float,
) -> dict[str, float | int | bool]:
    """Selected-Gaussian edge-margin diagnostics over true-adjacency pools.

    This mirrors :func:`edge_partial_correlation_margin`, but evaluates the
    exact selected Gaussian law induced by the centered quadratic mask.  It also
    reports exact query-retention probabilities for those audited edge queries.
    The query family is a diagnostic subset, not a claim that it equals every
    possible data-dependent PC query.
    """
    if max_conditioning_set_size < 0:
        raise ValueError('max_conditioning_set_size must be nonnegative')
    index={node:i for i,node in enumerate(nodes)}
    masked_idx={index[str(node)] for node in masked_nodes if str(node) in index}
    variances=np.diag(np.asarray(covariance,dtype=float))
    skeleton=graph.to_undirected()
    rhos=[]; rets=[]
    for u,v in sorted((str(u),str(v)) for u,v in skeleton.edges()):
        pools=(set(map(str,skeleton.neighbors(u)))-{v}, set(map(str,skeleton.neighbors(v)))-{u})
        conditioning_sets={()}
        for pool in pools:
            ordered=tuple(sorted(pool))
            for size in range(1,min(max_conditioning_set_size,len(ordered))+1):
                conditioning_sets.update(combinations(ordered,size))
        for cond in sorted(conditioning_sets):
            q=[index[u],index[v],*[index[x] for x in cond]]
            rho,ret=quadratic_selected_query_stats(
                covariance,q,population_variances=variances,masked_indices=masked_idx,
                quadratic_a=quadratic_a,quadratic_c=quadratic_c)
            if np.isfinite(rho): rhos.append(abs(float(rho)))
            if np.isfinite(ret): rets.append(float(ret))
    rho=np.asarray(rhos,dtype=float); ret=np.asarray(rets,dtype=float)
    return {
        'selected_edge_query_count': int(len(rho)),
        'selected_edge_partial_corr_min': float(rho.min()) if len(rho) else np.nan,
        'selected_edge_partial_corr_q10': float(np.quantile(rho,0.10)) if len(rho) else np.nan,
        'selected_edge_partial_corr_median': float(np.median(rho)) if len(rho) else np.nan,
        'selected_edge_partial_corr_max': float(rho.max()) if len(rho) else np.nan,
        'selected_edge_partial_corr_below_001': int(np.sum(rho<0.01)) if len(rho) else 0,
        'selected_edge_partial_corr_below_005': int(np.sum(rho<0.05)) if len(rho) else 0,
        'selected_edge_partial_corr_below_010': int(np.sum(rho<0.10)) if len(rho) else 0,
        'selected_edge_query_retention_min': float(ret.min()) if len(ret) else np.nan,
        'selected_edge_query_retention_q10': float(np.quantile(ret,0.10)) if len(ret) else np.nan,
        'selected_edge_query_retention_median': float(np.median(ret)) if len(ret) else np.nan,
        'selected_edge_query_retention_max': float(ret.max()) if len(ret) else np.nan,
        'selected_edge_diagnostics_finite': bool(len(rho) and len(ret) and np.all(np.isfinite(rho)) and np.all(np.isfinite(ret))),
    }

def pc_separator_depth_diagnostics(
    graph: nx.DiGraph,
    max_conditioning_set_size: int,
) -> dict[str, float | int | bool | str]:
    """Fast exact pass/fail audit of the bounded separator-depth premise.

    For every nonedge ``(x,y)``, the PC skeleton correctness argument requires
    a d-separating set of size at most ``d`` inside the *true* adjacency set of
    at least one endpoint.  A successful audit must therefore examine every
    nonedge.  A failed audit, however, needs only one certified counterexample.

    To avoid unnecessary enumeration on larger structures while preserving exact
    pass/fail semantics, nonedges are ordered by
    endpoint degree and the audit exits at the first unresolved pair.  Thus:

    * ``exhaustive_pass`` means the premise was checked for every nonedge and is
      true; coverage is exactly 1 and unresolved count exactly 0.
    * ``early_exit_failure_witness`` means a concrete nonedge was exhaustively
      checked through depth ``d`` and had no admissible separator.  This is an
      exact proof that the premise is false, but it is *not* an estimate of the
      fraction of all nonedges that would be resolvable.  Coverage/count fields
      that would require continuing the exhaustive scan are therefore NaN.

    This distinction prevents a structural premise diagnostic from becoming a
    large hidden runtime cost or a misleading pseudo-performance metric.
    """
    if max_conditioning_set_size < 0:
        raise ValueError("max_conditioning_set_size must be nonnegative")
    nodes = sorted(map(str, graph.nodes()))
    skeleton = graph.to_undirected()
    degree = {node: int(skeleton.degree(node)) for node in nodes}
    nonedges = [
        (x, y) for x, y in combinations(nodes, 2) if not skeleton.has_edge(x, y)
    ]
    # High-degree pairs are the most expensive and, empirically, the likeliest
    # to expose a depth mismatch.  This ordering changes only runtime, never the
    # pass/fail result.
    nonedges.sort(
        key=lambda xy: (
            -(degree[xy[0]] + degree[xy[1]]),
            -max(degree[xy[0]], degree[xy[1]]),
            xy[0], xy[1],
        )
    )
    tested_sets = 0
    minimal_calls = 0
    depths: list[int] = []
    pairs_checked = 0
    for x, y in nonedges:
        pairs_checked += 1
        pools = (
            set(map(str, skeleton.neighbors(x))) - {y},
            set(map(str, skeleton.neighbors(y))) - {x},
        )
        found_depth: int | None = None
        minimal_results: list[set[str] | None] = []
        # Fast exact-positive screen. NetworkX finds an inclusion-minimal
        # d-separator in linear time under a restricted candidate set. If one
        # returned separator already has size <= d, the pair is certified.
        # A larger inclusion-minimal separator does *not* prove that no smaller
        # alternative exists, so ambiguous cases fall back to exhaustive
        # enumeration through d.
        for pool in pools:
            minimal_calls += 1
            z = nx.find_minimal_d_separator(graph, {x}, {y}, restricted=pool)
            minimal_results.append(None if z is None else set(map(str, z)))
            if z is not None and len(z) <= max_conditioning_set_size:
                found_depth = int(len(z))
                break
        if found_depth is None and not all(z is None for z in minimal_results):
            for depth in range(max_conditioning_set_size + 1):
                candidates = {
                    tuple(cond)
                    for pool in pools
                    if len(pool) >= depth
                    for cond in combinations(tuple(sorted(pool)), depth)
                }
                for cond in sorted(candidates):
                    tested_sets += 1
                    if nx.is_d_separator(graph, {x}, {y}, set(cond)):
                        found_depth = depth
                        break
                if found_depth is not None:
                    break
        if found_depth is None:
            return {
                "oracle_nonedges": int(len(nonedges)),
                "oracle_nonedges_separator_within_d_alg": np.nan,
                "oracle_nonedges_unresolved_at_d_alg": np.nan,
                "oracle_nonedges_unresolved_at_d_alg_lower_bound": 1,
                "oracle_separator_coverage_fraction": np.nan,
                "oracle_separator_depth_max_found": np.nan,
                "oracle_separator_depth_mean_found": np.nan,
                "oracle_separator_candidate_sets_tested": int(tested_sets),
                "oracle_depth_minimal_separator_calls": int(minimal_calls),
                "oracle_depth_pairs_checked": int(pairs_checked),
                "oracle_depth_audit_mode": "early_exit_failure_witness",
                "oracle_depth_failure_witness_x": str(x),
                "oracle_depth_failure_witness_y": str(y),
                "oracle_search_depth_premise_satisfied": False,
            }
        depths.append(found_depth)

    arr = np.asarray(depths, dtype=float)
    total = len(nonedges)
    return {
        "oracle_nonedges": int(total),
        "oracle_nonedges_separator_within_d_alg": int(total),
        "oracle_nonedges_unresolved_at_d_alg": 0,
        "oracle_nonedges_unresolved_at_d_alg_lower_bound": 0,
        "oracle_separator_coverage_fraction": 1.0,
        "oracle_separator_depth_max_found": int(arr.max()) if len(arr) else 0,
        "oracle_separator_depth_mean_found": float(arr.mean()) if len(arr) else 0.0,
        "oracle_separator_candidate_sets_tested": int(tested_sets),
        "oracle_depth_minimal_separator_calls": int(minimal_calls),
        "oracle_depth_pairs_checked": int(pairs_checked),
        "oracle_depth_audit_mode": "exhaustive_pass",
        "oracle_depth_failure_witness_x": "",
        "oracle_depth_failure_witness_y": "",
        "oracle_search_depth_premise_satisfied": True,
    }


def oracle_pc_query_margin_diagnostics(
    graph: nx.DiGraph,
    covariance: np.ndarray,
    nodes: list[str],
    max_conditioning_set_size: int,
    *,
    null_tolerance: float = 1e-10,
    selected_quadratic_masked_nodes: set[str] | None = None,
    selected_quadratic_a: float | None = None,
    selected_quadratic_c: float | None = None,
) -> dict[str, float | int | bool]:
    """Audit population partial-correlation margins on the exact oracle-PC path.

    The search logic is two-sided PC-stable. Exact DAG d-separation supplies the
    truth label for each queried CI statement, while the linear-Gaussian
    covariance supplies its population partial correlation. This directly
    measures the smallest nonzero signal encountered by the implemented search
    rather than using edge coefficients as a faithfulness surrogate.
    """
    if max_conditioning_set_size < 0:
        raise ValueError("max_conditioning_set_size must be nonnegative")
    index = {str(node): i for i, node in enumerate(nodes)}
    variables = sorted(map(str, graph.nodes()))
    candidate = nx.Graph()
    candidate.add_nodes_from(variables)
    candidate.add_edges_from(combinations(variables, 2))
    dependent_abs: list[float] = []
    independent_abs: list[float] = []
    selected_dependent_abs: list[float] = []
    selected_independent_abs: list[float] = []
    selected_retentions: list[float] = []
    selected_enabled = (
        selected_quadratic_masked_nodes is not None
        and selected_quadratic_a is not None
        and selected_quadratic_c is not None
    )
    masked_idx = (
        {index[str(node)] for node in selected_quadratic_masked_nodes if str(node) in index}
        if selected_enabled else set()
    )
    variances = np.diag(np.asarray(covariance, dtype=float))
    tests = 0
    for level in range(max_conditioning_set_size + 1):
        snapshot = {node: set(candidate.neighbors(node)) for node in variables}
        any_testable = False
        for x, y in sorted(candidate.edges()):
            if not candidate.has_edge(x, y):
                continue
            adj_x = snapshot[x] - {y}
            adj_y = snapshot[y] - {x}
            if max(len(adj_x), len(adj_y)) < level:
                continue
            any_testable = True
            conds = {
                tuple(cond)
                for pool in (adj_x, adj_y)
                if len(pool) >= level
                for cond in combinations(tuple(sorted(pool)), level)
            }
            for cond in sorted(conds):
                tests += 1
                rho = partial_correlation_from_covariance(
                    covariance, index[x], index[y], [index[z] for z in cond]
                )
                dsep = bool(nx.is_d_separator(graph, {x}, {y}, set(cond)))
                if np.isfinite(rho):
                    if dsep:
                        independent_abs.append(abs(float(rho)))
                    else:
                        dependent_abs.append(abs(float(rho)))
                if selected_enabled:
                    rho_sel, retention_sel = quadratic_selected_query_stats(
                        covariance,
                        [index[x], index[y], *[index[z] for z in cond]],
                        population_variances=variances,
                        masked_indices=masked_idx,
                        quadratic_a=float(selected_quadratic_a),
                        quadratic_c=float(selected_quadratic_c),
                    )
                    if np.isfinite(rho_sel):
                        if dsep:
                            selected_independent_abs.append(abs(float(rho_sel)))
                        else:
                            selected_dependent_abs.append(abs(float(rho_sel)))
                    if np.isfinite(retention_sel):
                        selected_retentions.append(float(retention_sel))
                if dsep:
                    candidate.remove_edge(x, y)
                    break
        if not any_testable:
            break
    dep = np.asarray(dependent_abs, dtype=float)
    null = np.asarray(independent_abs, dtype=float)
    sdep = np.asarray(selected_dependent_abs, dtype=float)
    snull = np.asarray(selected_independent_abs, dtype=float)
    sret = np.asarray(selected_retentions, dtype=float)
    truth_edges = {
        frozenset((str(u), str(v))) for u, v in graph.to_undirected().edges()
    }
    estimate_edges = {
        frozenset((str(u), str(v))) for u, v in candidate.edges()
    }
    return {
        "oracle_pc_query_count": int(tests),
        "oracle_pc_dependent_query_count": int(len(dep)),
        "oracle_pc_independent_query_count": int(len(null)),
        "oracle_pc_dependent_partial_corr_min": float(dep.min()) if len(dep) else np.nan,
        "oracle_pc_dependent_partial_corr_q05": float(np.quantile(dep, 0.05)) if len(dep) else np.nan,
        "oracle_pc_dependent_partial_corr_q10": float(np.quantile(dep, 0.10)) if len(dep) else np.nan,
        "oracle_pc_dependent_partial_corr_median": float(np.median(dep)) if len(dep) else np.nan,
        "oracle_pc_dependent_below_001": int(np.sum(dep < 0.01)) if len(dep) else 0,
        "oracle_pc_dependent_below_005": int(np.sum(dep < 0.05)) if len(dep) else 0,
        "oracle_pc_dependent_below_010": int(np.sum(dep < 0.10)) if len(dep) else 0,
        "oracle_pc_null_partial_corr_max_abs": float(null.max()) if len(null) else 0.0,
        "oracle_pc_null_numeric_check": bool((null <= null_tolerance).all()) if len(null) else True,
        "oracle_pc_exact_skeleton": bool(estimate_edges == truth_edges),
        "oracle_pc_false_positive_edges": int(len(estimate_edges - truth_edges)),
        "oracle_pc_false_negative_edges": int(len(truth_edges - estimate_edges)),
        "selected_oracle_pc_dependent_partial_corr_min": float(sdep.min()) if len(sdep) else np.nan,
        "selected_oracle_pc_dependent_partial_corr_q05": float(np.quantile(sdep, 0.05)) if len(sdep) else np.nan,
        "selected_oracle_pc_dependent_partial_corr_q10": float(np.quantile(sdep, 0.10)) if len(sdep) else np.nan,
        "selected_oracle_pc_dependent_partial_corr_median": float(np.median(sdep)) if len(sdep) else np.nan,
        "selected_oracle_pc_null_partial_corr_max_abs": float(snull.max()) if len(snull) else (0.0 if selected_enabled else np.nan),
        "selected_oracle_pc_null_numeric_check": bool((snull <= null_tolerance).all()) if len(snull) else (True if selected_enabled else np.nan),
        "selected_oracle_pc_query_retention_min": float(sret.min()) if len(sret) else np.nan,
        "selected_oracle_pc_query_retention_q10": float(np.quantile(sret, 0.10)) if len(sret) else np.nan,
        "selected_oracle_pc_query_retention_median": float(np.median(sret)) if len(sret) else np.nan,
        "selected_oracle_pc_query_retention_max": float(sret.max()) if len(sret) else np.nan,
    }
