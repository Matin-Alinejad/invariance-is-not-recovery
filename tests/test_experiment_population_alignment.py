"""Regression tests for fixed-population SEM and sample-prefix alignment."""
from __future__ import annotations

import numpy as np

from src.algorithms.population_calibrated_missingness import inject_population_calibrated_missingness
from src.data_generation.synthetic_graphs import GraphTopology
from src.data_generation.linear_gaussian_sem import (
    generate_graph,
    generate_linear_gaussian_sample,
)
from src.data_generation.sem_diagnostics import linear_sem_covariance


def _weights(causal):
    return {
        node: tuple(float(x) for x in info["parameters"]["weights"])
        for node, info in causal.items()
    }


def test_structural_parameters_are_invariant_to_sample_size_and_rows_are_nested():
    graph = generate_graph(GraphTopology.RANDOM_REGULAR, 20, {"degree": 2}, 17)
    small = generate_linear_gaussian_sample(
        graph=graph, n_samples=800, seed=17, signal_low=0.5, signal_high=1.0
    )
    large = generate_linear_gaussian_sample(
        graph=graph, n_samples=1600, seed=17, signal_low=0.5, signal_high=1.0
    )
    assert _weights(small.causal_parameters) == _weights(large.causal_parameters)
    assert np.array_equal(small.data.to_numpy(), large.data.to_numpy()[:800])


def test_raw_sem_population_covariance_and_quadratic_calibration_align():
    graph = generate_graph(GraphTopology.RANDOM_REGULAR, 8, {"degree": 2}, 123)
    generated = generate_linear_gaussian_sample(
        graph=graph, n_samples=40000, seed=123, signal_low=0.5, signal_high=1.0
    )
    nodes, cov = linear_sem_covariance(graph, generated.causal_parameters)
    empirical = np.cov(generated.data.loc[:, nodes].to_numpy(), rowvar=False, ddof=0)
    # Large-sample covariance check protects the exact SEM/noise convention.
    scale = np.maximum(1.0, np.abs(cov))
    assert np.max(np.abs(empirical - cov) / scale) < 0.04

    pop_mean = {str(v): 0.0 for v in nodes}
    pop_std = {str(v): float(np.sqrt(cov[i, i])) for i, v in enumerate(nodes)}
    nonroots = sorted(str(v) for v in graph.nodes() if graph.in_degree(v) > 0)
    _, diag, extra = inject_population_calibrated_missingness(
        generated.data,
        mode="self_masking_gaussian_preserving",
        target_rate=0.30,
        seed=1000126,
        columns=nonroots,
        population_mean=pop_mean,
        population_std=pop_std,
        quadratic_a=0.2,
    )
    assert extra["calibration"] == "population_fixed"
    assert extra["quadratic_c"] <= 1.0
    assert abs(diag.realized_masked_cell_rate - 0.30) < 0.01


def test_population_masks_are_prefix_coupled_across_sample_sizes():
    graph = generate_graph(GraphTopology.RANDOM_REGULAR, 10, {"degree": 2}, 29)
    small = generate_linear_gaussian_sample(
        graph=graph, n_samples=600, seed=29, signal_low=0.5, signal_high=1.0
    )
    large = generate_linear_gaussian_sample(
        graph=graph, n_samples=1200, seed=29, signal_low=0.5, signal_high=1.0
    )
    nodes, cov = linear_sem_covariance(graph, small.causal_parameters)
    pop_mean = {str(v): 0.0 for v in nodes}
    pop_std = {str(v): float(np.sqrt(cov[i, i])) for i, v in enumerate(nodes)}
    nonroots = sorted(str(v) for v in graph.nodes() if graph.in_degree(v) > 0)

    for mode in ("self_masking_gaussian_preserving", "self_masking_logistic_population"):
        obs_small, _, _ = inject_population_calibrated_missingness(
            small.data,
            mode=mode,
            target_rate=0.30,
            seed=1_000_032,
            columns=nonroots,
            slope=1.0,
            population_mean=pop_mean,
            population_std=pop_std,
            quadratic_a=0.2,
        )
        obs_large, _, _ = inject_population_calibrated_missingness(
            large.data,
            mode=mode,
            target_rate=0.30,
            seed=1_000_032,
            columns=nonroots,
            slope=1.0,
            population_mean=pop_mean,
            population_std=pop_std,
            quadratic_a=0.2,
        )
        assert np.array_equal(
            obs_small.to_numpy(), obs_large.to_numpy()[: len(obs_small)], equal_nan=True
        )
