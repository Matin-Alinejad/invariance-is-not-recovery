"""Rigorous matched global/local causal-skeleton experiments.

The runner distinguishes three scientifically different objects on exactly the
same generated graph, observed sample, seed, and target set:

1. whole-skeleton test-wise-deletion PC;
2. the target neighborhood extracted from that global estimate;
3. a dedicated target-local test-wise-deletion PC search.

It reports precision, recall, F1, TP/FP/FN, exact recovery, normalized error,
CI-test counts, effective sample sizes, runtime, realized missingness, graph
complexity, and a deterministic F1 lower-bound audit.  Runs are deterministic,
resumable by a transparent scientific-condition ``cell_id``, and optionally parallel.
"""
from __future__ import annotations

import argparse
import json
import math
import random
import shutil
import sys
import time
import traceback
from dataclasses import asdict
from pathlib import Path
from typing import Any, Dict, Iterable, List, Mapping, Sequence, Tuple

import networkx as nx
import numpy as np
import pandas as pd
import yaml
from joblib import Parallel, delayed

REPO_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO_ROOT / "code"))

from experiments.execution_utils import (
    append_csv,
    assert_json_compatible,
    atomic_write_json,
    cell_id_from_mapping,
    completed_cell_ids,
    environment_manifest,
)
from src.algorithms.instrumented_pc import InstrumentedTestWiseDeletionPC
from src.algorithms.population_calibrated_missingness import inject_population_calibrated_missingness
from src.data_generation.synthetic_graphs import (
    DataGenerationModel,
    GraphTopology,
    NoiseDistribution,
    SyntheticDatasetConfig,
)
from src.data_generation.linear_gaussian_sem import (
    generate_graph,
    generate_linear_gaussian_sample,
)
from src.data_generation.sem_diagnostics import (
    edge_partial_correlation_margin,
    linear_sem_covariance,
    oracle_pc_query_margin_diagnostics,
    pc_separator_depth_diagnostics,
    quadratic_selected_edge_query_diagnostics,
)


def completed_graph_cell_ids(path: Path) -> set[str]:
    """Return only cells with a complete global/local row structure."""
    if not path.exists():
        return set()
    try:
        frame = pd.read_csv(path)
    except pd.errors.EmptyDataError:
        return set()
    required = {"cell_id", "cell_status", "evaluation_scope", "targets_per_graph_realized"}
    if not required.issubset(frame.columns):
        return set()
    if "local_search_method" not in frame.columns:
        frame["local_search_method"] = "pc_simple_heuristic"
    frame = frame[["cell_id", "cell_status", "evaluation_scope", "targets_per_graph_realized", "local_search_method"]]
    frame = frame[frame["cell_status"].fillna("complete") == "complete"]
    completed: set[str] = set()
    for cell_id, group in frame.groupby("cell_id", dropna=False):
        if pd.isna(cell_id) or group.empty:
            continue
        realized = int(group["targets_per_graph_realized"].iloc[0])
        counts = group["evaluation_scope"].value_counts()
        local_method = str(group["local_search_method"].iloc[0]) if "local_search_method" in group else "pc_simple_heuristic"
        expected_local = 0 if local_method == "none" else realized
        if (
            counts.get("global_whole_skeleton", 0) == 1
            and counts.get("target_restriction_of_global", 0) == realized
            and counts.get("dedicated_local", 0) == expected_local
            and len(group) == 1 + realized + expected_local
        ):
            completed.add(str(cell_id))
    return completed


def skeleton_edges(graph: nx.DiGraph | nx.Graph) -> set[frozenset[str]]:
    """Return the undirected edge set of a graph as order-invariant node pairs."""
    return {frozenset((str(u), str(v))) for u, v in graph.edges() if u != v}


def target_edges(graph: nx.DiGraph | nx.Graph, target: str) -> set[frozenset[str]]:
    """Return the target-incident skeleton edges used for local evaluation."""
    if not graph.has_node(target):
        return set()
    if isinstance(graph, nx.DiGraph):
        neighbors = set(graph.predecessors(target)) | set(graph.successors(target))
    else:
        neighbors = set(graph.neighbors(target))
    return {frozenset((target, str(node))) for node in neighbors if node != target}


def binary_metrics(truth: set, estimate: set) -> Dict[str, float | int | bool]:
    """Compute edge-set precision, recall, F1, exact recovery, and error diagnostics."""
    tp = len(truth & estimate)
    fp = len(estimate - truth)
    fn = len(truth - estimate)
    precision = tp / (tp + fp) if tp + fp else 0.0
    recall = tp / (tp + fn) if tp + fn else 0.0
    f1 = 2 * tp / (2 * tp + fp + fn) if 2 * tp + fp + fn else 0.0
    s = len(truth)
    total_error = fp + fn
    if 0 <= total_error < s:
        deterministic_lower = 2 * (s - total_error) / (2 * s + total_error)
    else:
        deterministic_lower = np.nan
    return {
        "tp": int(tp),
        "fp": int(fp),
        "fn": int(fn),
        "total_error": int(total_error),
        "normalized_total_error": float(total_error / s) if s else np.nan,
        "precision": float(precision),
        "recall": float(recall),
        "f1": float(f1),
        "exact_recovery": bool(total_error == 0),
        "deterministic_f1_lower": float(deterministic_lower),
        "deterministic_bound_verified": bool(
            np.isnan(deterministic_lower) or f1 + 1e-12 >= deterministic_lower
        ),
    }


def alpha_for(
    schedule: str, n: int, p: int, family_alpha: float = 0.05, d_alg: int = 0
) -> float:
    """Resolve the registered CI-test significance schedule for one graph cell."""
    if schedule == "fixed_005":
        return 0.05
    if schedule == "n_inverse_half":
        return min(family_alpha, n ** -0.5)
    if schedule == "n_inverse":
        return min(family_alpha, n ** -1.0)
    if schedule == "bonferroni_pairs":
        return family_alpha / max(1, p * (p - 1) // 2)
    if schedule == "bonferroni_pc_upper":
        # Conservative upper bound on the number of pair/conditioning-set
        # hypotheses attempted by a depth-d skeleton search.  This is a
        # multiplicity sensitivity schedule, not an independence assumption.
        if d_alg < 0:
            raise ValueError("d_alg must be nonnegative")
        conditioning_sets = sum(
            math.comb(max(0, p - 2), j)
            for j in range(min(int(d_alg), max(0, p - 2)) + 1)
        )
        family_size = (p * (p - 1) // 2) * conditioning_sets
        return family_alpha / max(1, family_size)
    raise ValueError(f"Unknown alpha schedule: {schedule}")


def calibrated_sample_size(
    p: int, gamma: float, reference_p: int, reference_n_over_p: float
) -> int:
    """Return the registered sample size under the power-law scaling schedule."""
    if p <= 0 or gamma <= 0 or reference_p <= 0 or reference_n_over_p <= 0:
        raise ValueError("Sample-scaling parameters must be positive")
    constant = reference_n_over_p * (reference_p ** (1.0 - gamma))
    return max(20, int(math.ceil(constant * (p ** gamma))))


def topology_spec(entry: Mapping[str, Any], p: int) -> Tuple[GraphTopology, Dict[str, Any]]:
    """Resolve a topology configuration into its enum and graph-law parameters."""
    topology = GraphTopology(entry["enum"])
    params = dict(entry.get("params", {}))
    if topology == GraphTopology.RANDOM and "average_degree" in entry:
        params["edge_prob"] = min(1.0, float(entry["average_degree"]) / max(1, p - 1))
    return topology, params


def scientific_topology_entry(entry: Mapping[str, Any]) -> Dict[str, Any]:
    """Strip grid-eligibility metadata from a topology's scientific identity.

    ``min_p``, ``max_p`` and a declarative single-``p`` selector decide whether
    a YAML grid includes a condition; they do not change the graph law once the
    top-level dimension ``p`` is fixed.  Excluding them makes identical cells
    share one content ID across primary/sensitivity configurations.
    """
    return {
        str(k): v for k, v in dict(entry).items()
        if str(k) not in {"min_p", "max_p", "p"}
    }



def realized_linear_weights(causal_parameters: Mapping[str, Any]) -> np.ndarray:
    """Collect finite realized linear SEM coefficients from cell metadata."""
    weights: List[float] = []
    for node_info in causal_parameters.values():
        params = node_info.get("parameters", {}) if isinstance(node_info, Mapping) else {}
        for weight in params.get("weights", []) or []:
            if np.isfinite(weight):
                weights.append(float(weight))
    return np.asarray(weights, dtype=float)

def choose_targets(
    graph: nx.DiGraph, count: int, seed: int, policy: str = "stratified_degree"
) -> List[str]:
    """Choose deterministic target nodes according to the registered sampling policy."""
    eligible = sorted((str(node) for node in graph.nodes() if graph.degree(node) > 0))
    if count <= 0:
        return []
    if policy == "all" or len(eligible) <= count:
        return eligible
    if policy == "random":
        return sorted(random.Random(seed).sample(eligible, count))
    if policy == "stratified_degree":
        ordered = sorted(eligible, key=lambda node: (graph.degree(node), node))
        indices = np.linspace(0, len(ordered) - 1, num=count, dtype=int)
        selected = [ordered[int(i)] for i in sorted(set(indices.tolist()))]
        # Rounding can produce duplicates. Fill deterministically from the
        # remaining degree-ordered nodes.
        if len(selected) < count:
            for node in ordered:
                if node not in selected:
                    selected.append(node)
                    if len(selected) == count:
                        break
        return sorted(selected)
    raise ValueError(f"Unknown target_sampling policy: {policy}")


def target_characteristics(graph: nx.DiGraph, target: str) -> Dict[str, Any]:
    """Summarize graph-theoretic properties of a selected target node."""
    undirected_degrees = np.asarray(list(dict(graph.to_undirected().degree()).values()), dtype=float)
    degree = int(graph.to_undirected().degree(target))
    degree_percentile = float(np.mean(undirected_degrees <= degree)) if len(undirected_degrees) else np.nan
    return {
        "target_in_degree": int(graph.in_degree(target)),
        "target_out_degree": int(graph.out_degree(target)),
        "target_is_root": bool(graph.in_degree(target) == 0),
        "target_is_leaf": bool(graph.out_degree(target) == 0),
        "target_degree_percentile": degree_percentile,
    }


def mask_columns(graph: nx.DiGraph, policy: str) -> List[str]:
    """Resolve which graph variables are subject to the configured missingness mechanism."""
    nodes = sorted(map(str, graph.nodes()))
    if policy == "all":
        return nodes
    if policy == "non_roots":
        return sorted(str(v) for v in graph.nodes() if graph.in_degree(v) > 0)
    if policy == "roots":
        return sorted(str(v) for v in graph.nodes() if graph.in_degree(v) == 0)
    raise ValueError(f"Unknown mask_variables policy: {policy}")


def flatten_trace_summary(prefix: str, summary: Mapping[str, float]) -> Dict[str, float]:
    """Prefix CI-trace summary fields before adding them to an output row."""
    return {f"{prefix}_{key}": value for key, value in summary.items()}


def write_trace(frame: pd.DataFrame, path: Path) -> str:
    """Write an optional full CI trace and return its repository-relative path."""
    path.parent.mkdir(parents=True, exist_ok=True)
    frame.to_csv(path, index=False, compression="gzip")
    return str(path)


def _scope_row(
    *,
    common: Mapping[str, Any],
    evaluation_scope: str,
    algorithm: str,
    target: str,
    truth_scope: set,
    estimate_scope: set,
    candidate_edges: int,
    target_degree: float,
    target_info: Mapping[str, Any] | None,
    fit_runtime: float,
    evaluation_runtime: float,
    trace_summary: Mapping[str, float],
    trace_file: str,
) -> Dict[str, Any]:
    metrics = binary_metrics(truth_scope, estimate_scope)
    return {
        **common,
        "cell_status": "complete",
        "evaluation_scope": evaluation_scope,
        "algorithm": algorithm,
        "target": target,
        "target_degree": target_degree,
        "target_degree_gt_d_alg": bool(target_degree > float(common.get("d_alg", np.inf))) if np.isfinite(target_degree) else np.nan,
        **(dict(target_info) if target_info is not None else {
            "target_in_degree": np.nan,
            "target_out_degree": np.nan,
            "target_is_root": np.nan,
            "target_is_leaf": np.nan,
            "target_degree_percentile": np.nan,
        }),
        "true_edges_scope": len(truth_scope),
        "candidate_edges_scope": int(candidate_edges),
        "class_prevalence": float(len(truth_scope) / candidate_edges) if candidate_edges else np.nan,
        "fit_runtime_seconds": float(fit_runtime),
        "evaluation_runtime_seconds": float(evaluation_runtime),
        "task_runtime_seconds": float(fit_runtime + evaluation_runtime),
        "runtime_seconds": float(fit_runtime + evaluation_runtime),
        **metrics,
        **flatten_trace_summary("trace", trace_summary),
        "trace_file": trace_file,
    }


def run_cell(spec: Mapping[str, Any], output_dir: Path, trace_mode: str) -> Tuple[List[Dict[str, Any]], Dict[str, Any] | None]:
    """Execute one registered graph cell and return its evaluation rows and failure record."""
    cell_id = str(spec["cell_id"])
    try:
        p = int(spec["p"])
        gamma = float(spec["gamma"])
        seed = int(spec["seed"])
        n = calibrated_sample_size(
            p, gamma, int(spec["reference_p"]), float(spec["reference_n_over_p"])
        )
        alpha = alpha_for(
            str(spec["alpha_schedule"]), n, p, d_alg=int(spec["max_conditioning_set_size"])
        )
        topology, topology_params = topology_spec(spec["topology_entry"], p)
        # Population-calibration invariant: do not standardize using statistics from the
        # same realized sample. The linear-Gaussian SEM covariance reconstructed
        # below is the population law used to calibrate the fixed self-masking
        # functions. Sample-fitted StandardScaler would make each row's mask
        # depend on all other rows and would break the iid fixed-thinning premise.
        topology_params = dict(topology_params)
        topology_params["standardize"] = False
        model = DataGenerationModel(str(spec["sem_model"]))
        noise = NoiseDistribution(str(spec["noise_distribution"]))

        dataset_config = SyntheticDatasetConfig(
            name=cell_id,
            n_variables=p,
            n_samples=n,
            topology=topology,
            generation_model=model,
            noise_distribution=noise,
            causal_strength_range=(float(spec["signal_low"]), float(spec["signal_high"])),
            random_seed=seed,
            topology_params=topology_params,
        )
        if model != DataGenerationModel.LINEAR or noise != NoiseDistribution.GAUSSIAN:
            raise ValueError("Registered recovery runner requires linear-Gaussian SEMs")
        truth = generate_graph(topology, p, topology_params, seed)
        generated = generate_linear_gaussian_sample(
            graph=truth,
            n_samples=n,
            seed=seed,
            signal_low=float(spec["signal_low"]),
            signal_high=float(spec["signal_high"]),
        )
        complete = generated.data.replace([np.inf, -np.inf], np.nan)
        finite_complete = complete.to_numpy(dtype=float)
        max_abs_complete_value = float(np.nanmax(np.abs(finite_complete))) if finite_complete.size else 0.0
        ci_sanitizer_max_abs = 1e12

        # Population parameters are computed BEFORE missingness and are fixed independently
        # of the realized sample used for evaluation. This is theorem-aligned calibration.
        if model != DataGenerationModel.LINEAR or noise != NoiseDistribution.GAUSSIAN:
            raise ValueError("Registered recovery runner currently requires linear-Gaussian SEMs")
        sem_nodes_pre, sem_cov_pre = linear_sem_covariance(truth, generated.causal_parameters)
        pop_mean = {str(node): 0.0 for node in sem_nodes_pre}
        pop_std = {str(node): float(np.sqrt(sem_cov_pre[i,i])) for i,node in enumerate(sem_nodes_pre)}
        selected_mask_columns = mask_columns(truth, str(spec["mask_variables"]))
        observed, missing_diag, missing_extra = inject_population_calibrated_missingness(
            complete,
            mode=str(spec["missingness_mode"]),
            target_rate=float(spec["missing_rate"]),
            seed=seed + 1_000_003,
            columns=selected_mask_columns,
            slope=float(spec["masking_slope"]),
            population_mean=pop_mean,
            population_std=pop_std,
            quadratic_a=float(spec.get("quadratic_a", 0.2)),
        )
        targets = choose_targets(
            truth,
            int(spec["targets_per_graph"]),
            seed + 2_000_003,
            policy=str(spec["target_sampling"]),
        )

        degree_values = list(dict(truth.to_undirected().degree()).values())
        realized_weights = realized_linear_weights(generated.causal_parameters)
        abs_weights = np.abs(realized_weights)
        d_alg = int(spec["max_conditioning_set_size"])
        degree_array = np.asarray(degree_values, dtype=float)
        structural_diagnostics: Dict[str, Any] = {
            "d_alg_covers_d_max": bool(max(degree_values, default=0) <= d_alg),
            "fraction_nodes_degree_gt_d_alg": float(np.mean(degree_array > d_alg)) if len(degree_array) else 0.0,
            **pc_separator_depth_diagnostics(truth, d_alg),
        }
        if model == DataGenerationModel.LINEAR and noise == NoiseDistribution.GAUSSIAN:
            sem_nodes, sem_covariance = linear_sem_covariance(truth, generated.causal_parameters)
            depth_ok = bool(structural_diagnostics["oracle_search_depth_premise_satisfied"])
            edge_margin_defaults = {
                "oracle_edge_query_count": np.nan,
                "oracle_edge_partial_corr_min": np.nan,
                "oracle_edge_partial_corr_q10": np.nan,
                "oracle_edge_partial_corr_median": np.nan,
                "oracle_edge_partial_corr_below_001": np.nan,
                "oracle_edge_partial_corr_below_005": np.nan,
                "oracle_edge_partial_corr_below_010": np.nan,
                "oracle_edge_margin_finite": np.nan,
                "oracle_edge_margin_diagnostics_run": False,
                "oracle_edge_margin_diagnostics_skip_reason": "",
            }
            structural_diagnostics.update(edge_margin_defaults)
            if depth_ok:
                structural_diagnostics.update(
                    edge_partial_correlation_margin(truth, sem_covariance, sem_nodes, d_alg)
                )
                structural_diagnostics["oracle_edge_margin_diagnostics_run"] = True
            else:
                structural_diagnostics["oracle_edge_margin_diagnostics_skip_reason"] = "depth_premise_false"

            # The theorem-preserving quadratic arm has an exact selected Gaussian
            # law.  Audit the selected-law nonzero edge margins and exact query
            # retention on the sparse true-adjacency diagnostic family.
            selected_edge_defaults = {
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
            structural_diagnostics.update(selected_edge_defaults)
            if depth_ok and str(spec["missingness_mode"]) == "self_masking_gaussian_preserving":
                qa = float(missing_extra.get("quadratic_a", np.nan))
                qc = float(missing_extra.get("quadratic_c", np.nan))
                structural_diagnostics.update(
                    quadratic_selected_edge_query_diagnostics(
                        truth, sem_covariance, sem_nodes, d_alg,
                        masked_nodes=set(selected_mask_columns),
                        quadratic_a=qa, quadratic_c=qc,
                    )
                )

            oracle_query_max_p = int(spec.get("oracle_query_diagnostics_max_p", 50))
            oracle_defaults = {
                "oracle_pc_query_count": np.nan,
                "oracle_pc_dependent_query_count": np.nan,
                "oracle_pc_independent_query_count": np.nan,
                "oracle_pc_dependent_partial_corr_min": np.nan,
                "oracle_pc_dependent_partial_corr_q05": np.nan,
                "oracle_pc_dependent_partial_corr_q10": np.nan,
                "oracle_pc_dependent_partial_corr_median": np.nan,
                "oracle_pc_dependent_below_001": np.nan,
                "oracle_pc_dependent_below_005": np.nan,
                "oracle_pc_dependent_below_010": np.nan,
                "oracle_pc_null_partial_corr_max_abs": np.nan,
                "oracle_pc_null_numeric_check": np.nan,
                "oracle_pc_exact_skeleton": np.nan,
                "oracle_pc_false_positive_edges": np.nan,
                "oracle_pc_false_negative_edges": np.nan,
                "selected_oracle_pc_dependent_partial_corr_min": np.nan,
                "selected_oracle_pc_dependent_partial_corr_q05": np.nan,
                "selected_oracle_pc_dependent_partial_corr_q10": np.nan,
                "selected_oracle_pc_dependent_partial_corr_median": np.nan,
                "selected_oracle_pc_null_partial_corr_max_abs": np.nan,
                "selected_oracle_pc_null_numeric_check": np.nan,
                "selected_oracle_pc_query_retention_min": np.nan,
                "selected_oracle_pc_query_retention_q10": np.nan,
                "selected_oracle_pc_query_retention_median": np.nan,
                "selected_oracle_pc_query_retention_max": np.nan,
                "oracle_pc_query_diagnostics_run": False,
                "oracle_pc_query_diagnostics_skip_reason": "",
            }
            structural_diagnostics.update(oracle_defaults)
            if p <= oracle_query_max_p and depth_ok:
                kwargs: Dict[str, Any] = {}
                if str(spec["missingness_mode"]) == "self_masking_gaussian_preserving":
                    kwargs = {
                        "selected_quadratic_masked_nodes": set(selected_mask_columns),
                        "selected_quadratic_a": float(missing_extra["quadratic_a"]),
                        "selected_quadratic_c": float(missing_extra["quadratic_c"]),
                    }
                structural_diagnostics.update(
                    oracle_pc_query_margin_diagnostics(
                        truth, sem_covariance, sem_nodes, d_alg, **kwargs
                    )
                )
                structural_diagnostics["oracle_pc_query_diagnostics_run"] = True
            elif not depth_ok:
                structural_diagnostics["oracle_pc_query_diagnostics_skip_reason"] = "depth_premise_false"
            else:
                structural_diagnostics["oracle_pc_query_diagnostics_skip_reason"] = "p_above_exact_query_audit_limit"
        else:
            structural_diagnostics.update({
                "oracle_edge_query_count": 0,
                "oracle_edge_partial_corr_min": np.nan,
                "oracle_edge_partial_corr_q10": np.nan,
                "oracle_edge_partial_corr_median": np.nan,
                "oracle_edge_partial_corr_below_001": np.nan,
                "oracle_edge_partial_corr_below_005": np.nan,
                "oracle_edge_partial_corr_below_010": np.nan,
                "oracle_edge_margin_finite": np.nan,
                "oracle_pc_query_diagnostics_run": False,
                "oracle_pc_query_diagnostics_skip_reason": "non_gaussian_sem",
            })

        depth_ok = bool(structural_diagnostics.get("oracle_search_depth_premise_satisfied", False))
        mode_name = str(spec["missingness_mode"])
        if mode_name == "self_masking_logistic_population":
            theorem_scope_class = "distribution_and_depth_stress" if not depth_ok else "distribution_stress"
        else:
            theorem_scope_class = "depth_stress" if not depth_ok else "gaussian_preserving_depth_covered"
        common: Dict[str, Any] = {
            "cell_id": cell_id,
            "p": p,
            "n": n,
            "gamma": gamma,
            "topology": str(spec["topology_name"]),
            "topology_params": json.dumps(topology_params, sort_keys=True),
            "sem_model": str(spec["sem_model"]),
            "noise_distribution": str(spec["noise_distribution"]),
            "signal_low": float(spec["signal_low"]),
            "signal_high": float(spec["signal_high"]),
            "realized_min_abs_weight": float(abs_weights.min()) if len(abs_weights) else np.nan,
            "realized_median_abs_weight": float(np.median(abs_weights)) if len(abs_weights) else np.nan,
            "realized_max_abs_weight": float(abs_weights.max()) if len(abs_weights) else np.nan,
            "missingness_mode": str(spec["missingness_mode"]),
            "theorem_scope_class": theorem_scope_class,
            "missing_rate_target": float(spec["missing_rate"]),
            "missing_rate_realized_all_cells": missing_diag.realized_cell_rate,
            "missing_rate_realized_masked_cells": missing_diag.realized_masked_cell_rate,
            "complete_row_rate": missing_diag.complete_row_rate,
            "masked_column_count": len(selected_mask_columns),
            "mask_variables": str(spec["mask_variables"]),
            "masking_slope": float(spec["masking_slope"]),
            "mask_calibration": str(missing_extra.get("calibration", "")),
            "data_standardization": "none_dedicated_population_sem_raw",
            "max_abs_complete_value": max_abs_complete_value,
            "ci_sanitizer_max_abs": ci_sanitizer_max_abs,
            "ci_sanitizer_clipping_inactive": bool(max_abs_complete_value < ci_sanitizer_max_abs),
            "quadratic_a_realized": missing_extra.get("quadratic_a", np.nan),
            "quadratic_c_realized": missing_extra.get("quadratic_c", np.nan),
            "alpha_schedule": str(spec["alpha_schedule"]),
            "alpha": alpha,
            "ci_test": str(spec["ci_test"]),
            "d_alg": d_alg,
            "min_effective_samples": int(spec["min_effective_samples"]),
            "insufficient_policy": str(spec["insufficient_policy"]),
            "d_max": max(degree_values, default=0),
            "avg_degree": float(np.mean(degree_values)) if degree_values else 0.0,
            "true_edges_graph": len(skeleton_edges(truth)),
            "seed": seed,
            "targets_per_graph_requested": int(spec["targets_per_graph"]),
            "target_sampling": str(spec["target_sampling"]),
            "targets_per_graph_realized": len(targets),
            "local_search_method": str(spec.get("local_search_method", "pc_simple_heuristic")),
            **structural_diagnostics,
        }

        record_trace = trace_mode == "full"
        global_algo = InstrumentedTestWiseDeletionPC(
            alpha=alpha,
            max_conditioning_set_size=int(spec["max_conditioning_set_size"]),
            missing_data_method="test_wise_deletion",
            record_trace=record_trace,
            min_effective_samples=int(spec["min_effective_samples"]),
            insufficient_policy=str(spec["insufficient_policy"]),
            ci_test=str(spec["ci_test"]),
        )
        t0 = time.perf_counter()
        global_est, global_trace = global_algo.fit_with_trace(observed)
        global_runtime = time.perf_counter() - t0
        global_trace_file = ""
        if record_trace:
            trace_path = output_dir / "traces" / f"{cell_id}_global.csv.gz"
            write_trace(global_trace, trace_path)
            global_trace_file = str(trace_path.relative_to(output_dir))
        global_summary = global_algo.trace_summary()

        rows: List[Dict[str, Any]] = []
        truth_global = skeleton_edges(truth)
        est_global = skeleton_edges(global_est)
        eval_t0 = time.perf_counter()
        global_metrics_row = _scope_row(
            common=common,
            evaluation_scope="global_whole_skeleton",
            algorithm="global_test_wise_deletion_pc",
            target="",
            truth_scope=truth_global,
            estimate_scope=est_global,
            candidate_edges=p * (p - 1) // 2,
            target_degree=np.nan,
            target_info=None,
            fit_runtime=global_runtime,
            evaluation_runtime=time.perf_counter() - eval_t0,
            trace_summary=global_summary,
            trace_file=global_trace_file,
        )
        rows.append(global_metrics_row)

        for target in targets:
            truth_local = target_edges(truth, target)
            target_info = target_characteristics(truth, target)
            eval_t0 = time.perf_counter()
            restricted_est = target_edges(global_est, target)
            rows.append(
                _scope_row(
                    common=common,
                    evaluation_scope="target_restriction_of_global",
                    algorithm="global_test_wise_deletion_pc",
                    target=target,
                    truth_scope=truth_local,
                    estimate_scope=restricted_est,
                    candidate_edges=p - 1,
                    target_degree=float(len(truth_local)),
                    target_info=target_info,
                    fit_runtime=global_runtime,
                    evaluation_runtime=time.perf_counter() - eval_t0,
                    trace_summary=global_summary,
                    trace_file=global_trace_file,
                )
            )

            local_method = str(spec.get("local_search_method", "pc_simple_heuristic"))
            if local_method != "none":
                local_algo = InstrumentedTestWiseDeletionPC(
                    alpha=alpha,
                    max_conditioning_set_size=int(spec["max_conditioning_set_size"]),
                    missing_data_method="test_wise_deletion",
                    record_trace=record_trace,
                    min_effective_samples=int(spec["min_effective_samples"]),
                    insufficient_policy=str(spec["insufficient_policy"]),
                    ci_test=str(spec["ci_test"]),
                )
                local_t0 = time.perf_counter()
                if local_method == "pc_simple_heuristic":
                    local_est, local_trace = local_algo.fit_local_with_trace(observed, target)
                    local_algorithm_label = "target_pc_simple_heuristic"
                elif local_method == "bounded_separator_exhaustive":
                    local_est, local_trace = local_algo.fit_target_bounded_separator_with_trace(observed, target)
                    local_algorithm_label = "target_bounded_separator_search"
                else:
                    raise ValueError(f"Unknown local_search_method: {local_method}")
                local_runtime = time.perf_counter() - local_t0
                local_trace_file = ""
                if record_trace:
                    local_path = output_dir / "traces" / f"{cell_id}_local_{target}.csv.gz"
                    write_trace(local_trace, local_path)
                    local_trace_file = str(local_path.relative_to(output_dir))
                local_summary = local_algo.trace_summary()
                eval_t0 = time.perf_counter()
                local_est_scope = target_edges(local_est, target)
                rows.append(
                    _scope_row(
                        common=common,
                        evaluation_scope="dedicated_local",
                        algorithm=local_algorithm_label,
                        target=target,
                        truth_scope=truth_local,
                        estimate_scope=local_est_scope,
                        candidate_edges=p - 1,
                        target_degree=float(len(truth_local)),
                        target_info=target_info,
                        fit_runtime=local_runtime,
                        evaluation_runtime=time.perf_counter() - eval_t0,
                        trace_summary=local_summary,
                        trace_file=local_trace_file,
                    )
                )


        metadata = {
            "cell_spec": dict(spec),
            "dataset_config": asdict(dataset_config),
            "truth_edges": sorted([sorted(tuple(edge)) for edge in truth_global]),
            "targets": targets,
            "missingness": asdict(missing_diag),
            "missingness_population_calibration": missing_extra,
            "causal_parameters": generated.causal_parameters,
        }
        atomic_write_json(output_dir / "metadata" / f"{cell_id}.json", metadata)
        return rows, None
    except Exception as exc:  # one failed cell must not destroy a multi-hour run
        failure = {
            "cell_id": cell_id,
            "cell_status": "failed",
            "error_type": type(exc).__name__,
            "error_message": str(exc),
            "traceback": traceback.format_exc(),
            "cell_spec": json.dumps(dict(spec), sort_keys=True, default=str),
        }
        return [], failure


def expand_specs(config: Mapping[str, Any], quick: bool = False) -> List[Dict[str, Any]]:
    """Expand a YAML experiment grid into deterministic graph-cell specifications."""
    base = dict(config["base"])
    if quick:
        p_grid = [10]
        gammas = [1.0]
        topologies = [config["topologies"][0]]
        sem_models = ["linear"]
        signal_ranges = [[0.5, 1.0]]
        missing_rates = [0.0, 0.3]
        missingness_modes = ["complete", "self_masking_gaussian_preserving", "self_masking_logistic_population"]
        masking_slopes = [1.0]
        alpha_schedules = ["fixed_005"]
        ci_tests = ["pearson"]
        seeds = [0]
        targets_per_graph = 2
        conditioning_sizes = [int(base["max_conditioning_set_size"])]
        min_effective_values = [int(base.get("min_effective_samples", 10))]
        insufficient_policies = [str(base.get("insufficient_policy", "keep_edge"))]
        local_methods = [str(base.get("local_search_method", "pc_simple_heuristic"))]
    else:
        p_grid = config["p_grid"]
        gammas = config["sample_scaling"]["gammas"]
        topologies = config["topologies"]
        sem_models = config["sem_models"]
        signal_ranges = config["signal_ranges"]
        missing_rates = config["missing_rates"]
        missingness_modes = config.get("missingness_modes", [base.get("missingness_mode", "self_masking")])
        masking_slopes = config.get("masking_slopes", [base.get("masking_slope", 1.0)])
        alpha_schedules = config["alpha_schedules"]
        ci_tests = config.get("ci_tests", [base.get("ci_test", "pearson")])
        seeds = base["seeds"]
        targets_per_graph = base["targets_per_graph"]
        conditioning_sizes = config.get(
            "max_conditioning_set_sizes", [base["max_conditioning_set_size"]]
        )
        min_effective_values = config.get(
            "min_effective_samples_values", [base.get("min_effective_samples", 10)]
        )
        insufficient_policies = config.get(
            "insufficient_policies", [base.get("insufficient_policy", "keep_edge")]
        )
        local_methods = config.get(
            "local_search_methods", [base.get("local_search_method", "pc_simple_heuristic")]
        )

    specs: List[Dict[str, Any]] = []
    for p in p_grid:
        for gamma in gammas:
            for topology_entry in topologies:
                declared_p = topology_entry.get("p")
                if declared_p is not None and int(declared_p) != int(p):
                    continue
                if topology_entry.get("min_p") is not None and int(p) < int(topology_entry["min_p"]):
                    continue
                if topology_entry.get("max_p") is not None and int(p) > int(topology_entry["max_p"]):
                    continue
                for sem_model in sem_models:
                    for signal_range in signal_ranges:
                        for missing_rate in missing_rates:
                            for missingness_mode in missingness_modes:
                                if missingness_mode == "complete" and float(missing_rate) != 0.0:
                                    continue
                                if missingness_mode != "complete" and float(missing_rate) == 0.0:
                                    # This is scientifically identical to complete data; avoid duplicate cells.
                                    continue
                                for masking_slope in masking_slopes:
                                    if missingness_mode == "complete" and masking_slope != masking_slopes[0]:
                                        continue
                                    for alpha_schedule in alpha_schedules:
                                        for ci_test in ci_tests:
                                            for conditioning_size in conditioning_sizes:
                                                for min_effective in min_effective_values:
                                                    for insufficient_policy in insufficient_policies:
                                                        for local_search_method in local_methods:
                                                            for seed in seeds:
                                                                payload: Dict[str, Any] = {
                                                                    "p": int(p),
                                                                    "gamma": float(gamma),
                                                                    "topology_name": topology_entry["name"],
                                                                    "topology_entry": scientific_topology_entry(topology_entry),
                                                                    "sem_model": str(sem_model),
                                                                    "noise_distribution": str(base.get("noise_distribution", "gaussian")),
                                                                    "signal_low": float(signal_range[0]),
                                                                    "signal_high": float(signal_range[1]),
                                                                    "missing_rate": float(missing_rate),
                                                                    "missingness_mode": str(missingness_mode),
                                                                    "masking_slope": float(masking_slope),
                                                                    "quadratic_a": float(base.get("quadratic_a", 0.2)),
                                                                    "mask_variables": str(base.get("mask_variables", "non_roots")),
                                                                    "alpha_schedule": str(alpha_schedule),
                                                                    "ci_test": str(ci_test),
                                                                    "max_conditioning_set_size": int(conditioning_size),
                                                                    "min_effective_samples": int(min_effective),
                                                                    "insufficient_policy": str(insufficient_policy),
                                                                    "local_search_method": str(local_search_method),
                                                                    "targets_per_graph": int(targets_per_graph),
                                                                    "target_sampling": str(base.get("target_sampling", "stratified_degree")),
                                                                    "seed": int(seed),
                                                                    "reference_p": int(base["reference_p"]),
                                                                    "reference_n_over_p": float(base["reference_n_over_p"]),
                                                                    "oracle_query_diagnostics_max_p": int(base.get("oracle_query_diagnostics_max_p", 50)),
                                                                }
                                                                payload["cell_id"] = cell_id_from_mapping(payload)
                                                                specs.append(payload)
    return specs


def _batches(items: Sequence[Any], size: int) -> Iterable[Sequence[Any]]:
    for start in range(0, len(items), size):
        yield items[start : start + size]


def main() -> None:
    """Parse CLI arguments, execute the requested cells, and write reproducible outputs."""
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--config", required=True)
    parser.add_argument("--output-dir")
    parser.add_argument("--quick", action="store_true")
    parser.add_argument("--fresh", action="store_true")
    parser.add_argument("--n-jobs", type=int, default=1)
    parser.add_argument("--trace-mode", choices=["none", "summary", "full"], default="summary")
    parser.add_argument("--max-cells", type=int)
    parser.add_argument("--num-shards", type=int, default=1)
    parser.add_argument("--shard-index", type=int, default=0)
    parser.add_argument("--fail-fast", action="store_true")
    args = parser.parse_args()

    config_path = Path(args.config).resolve()
    config = yaml.safe_load(config_path.read_text())
    output_dir = Path(args.output_dir).resolve() if args.output_dir else REPO_ROOT / config["output_dir"]
    output_dir.mkdir(parents=True, exist_ok=True)
    results_path = output_dir / "results.csv"
    failures_path = output_dir / "failures.csv"
    resolved_spec = {
        "config": config,
        "execution_mode": "quick" if args.quick else "full",
        "trace_mode": args.trace_mode,
        # Freeze shard assignment/coverage in the resumability contract.  This
        # prevents accidentally resuming shard 1 into a shard-0 directory (or
        # changing a max-cells truncation) while still sharing the same code
        "num_shards": int(args.num_shards),
        "shard_index": int(args.shard_index),
        "max_cells": None if args.max_cells is None else int(args.max_cells),
    }
    resolved_path = output_dir / "resolved_config.json"
    if args.fresh:
        for path in [results_path, failures_path, resolved_path, output_dir / "environment.json"]:
            if path.exists():
                path.unlink()
        for directory in [output_dir / "metadata", output_dir / "traces"]:
            if directory.exists():
                shutil.rmtree(directory)
    else:
        assert_json_compatible(resolved_path, resolved_spec)

    atomic_write_json(resolved_path, resolved_spec)
    environment = environment_manifest(REPO_ROOT, sys.argv)
    atomic_write_json(output_dir / "environment.json", environment)

    specs = expand_specs(config, quick=args.quick)
    if args.num_shards < 1 or not 0 <= args.shard_index < args.num_shards:
        raise ValueError("Require num_shards >= 1 and 0 <= shard_index < num_shards")
    specs = [spec for i, spec in enumerate(specs) if i % args.num_shards == args.shard_index]
    if args.max_cells is not None:
        limit = max(0, int(args.max_cells))
        if limit < len(specs):
            if limit == 0:
                specs = []
            else:
                indices = np.linspace(0, len(specs) - 1, num=limit, dtype=int)
                specs = [specs[int(i)] for i in sorted(set(indices.tolist()))]
    done = completed_graph_cell_ids(results_path)
    pending = [spec for spec in specs if str(spec["cell_id"]) not in done]
    print(f"Planned cells: {len(specs)}; completed: {len(done)}; pending: {len(pending)}")

    batch_size = max(1, abs(args.n_jobs) * 2 if args.n_jobs != 0 else 2)
    completed_now = 0
    failed_now = 0
    for batch in _batches(pending, batch_size):
        if args.n_jobs == 1:
            outputs = [run_cell(spec, output_dir, args.trace_mode) for spec in batch]
        else:
            outputs = Parallel(n_jobs=args.n_jobs, backend="loky")(
                delayed(run_cell)(spec, output_dir, args.trace_mode) for spec in batch
            )
        for rows, failure in outputs:
            if rows:
                append_csv(results_path, rows)
                completed_now += 1
            if failure is not None:
                append_csv(failures_path, [failure])
                failed_now += 1
                print(f"FAILED {failure['cell_id']}: {failure['error_type']}: {failure['error_message']}")
                if args.fail_fast:
                    raise RuntimeError(failure["error_message"])
        print(f"Progress: {completed_now}/{len(pending)} completed; {failed_now} failed", flush=True)

    print(f"Results: {results_path}")
    if failed_now:
        print(f"Failures: {failures_path}")


if __name__ == "__main__":
    main()
