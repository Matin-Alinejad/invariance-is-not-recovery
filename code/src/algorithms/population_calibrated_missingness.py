"""Population-calibrated missingness mechanisms for the registered recovery study.

Mask parameters are fixed from the population model, never estimated from the
same realized sample that is subsequently masked. This preserves the intended
population-level self-masking law and keeps matched sample-size comparisons
prefix-coupled under the registered random streams.
"""
from __future__ import annotations

from typing import Mapping, Optional, Sequence

import numpy as np
import pandas as pd

from src.algorithms.missingness_mechanisms import MissingnessDiagnostics, _logistic


def _normal_expectation_gh(fn, order: int = 80) -> float:
    """Approximate an expectation under a standard normal law by Gauss-Hermite quadrature."""
    nodes, weights = np.polynomial.hermite.hermgauss(int(order))
    z = np.sqrt(2.0) * nodes
    return float(np.sum(weights * fn(z)) / np.sqrt(np.pi))


def calibrate_population_logistic_intercept(
    target_missing_rate: float,
    slope: float,
    order: int = 80,
) -> float:
    """Calibrate a logistic self-masking intercept from the population Gaussian law."""
    if not 0.0 < target_missing_rate < 1.0:
        raise ValueError("target_missing_rate must lie in (0,1)")

    lower, upper = -40.0, 40.0
    for _ in range(120):
        midpoint = (lower + upper) / 2.0
        rate = _normal_expectation_gh(
            lambda z: _logistic(slope * z + midpoint),
            order=order,
        )
        if rate < target_missing_rate:
            lower = midpoint
        else:
            upper = midpoint
    return (lower + upper) / 2.0


def choose_quadratic_a(target_retention: float, requested_a: float) -> float:
    """Choose the largest safe quadratic coefficient not exceeding ``requested_a``."""
    if not 0.0 < target_retention <= 1.0:
        raise ValueError("target_retention must lie in (0,1]")
    if requested_a <= 0:
        raise ValueError("requested_a must be positive")

    maximum_a = max(1e-12, 1.0 / (target_retention**2) - 1.0)
    return min(float(requested_a), 0.95 * maximum_a)


def inject_population_calibrated_missingness(
    data: pd.DataFrame,
    *,
    mode: str,
    target_rate: float,
    seed: int,
    columns: Optional[Sequence[str]] = None,
    slope: float = 1.0,
    population_mean: Optional[Mapping[str, float]] = None,
    population_std: Optional[Mapping[str, float]] = None,
    quadratic_a: float = 0.2,
):
    """Apply population-calibrated self-masking with deterministic mask randomness."""
    allowed_modes = {
        "complete",
        "self_masking_logistic_population",
        "self_masking_gaussian_preserving",
    }
    if mode not in allowed_modes:
        raise ValueError(f"Unknown mode {mode}; expected {sorted(allowed_modes)}")
    if not 0.0 <= target_rate < 1.0:
        raise ValueError("target_rate must be in [0,1)")

    selected_columns = list(columns) if columns is not None else list(map(str, data.columns))
    output = data.copy()
    rng = np.random.default_rng(int(seed))

    if mode == "complete" or target_rate == 0.0 or not selected_columns:
        per_column_rate = {
            str(column): float(output[column].isna().mean()) for column in output.columns
        }
        diagnostics = MissingnessDiagnostics(
            mode="complete",
            target_rate=float(target_rate),
            realized_cell_rate=float(output.isna().to_numpy().mean()),
            realized_masked_cell_rate=(
                float(output.loc[:, selected_columns].isna().to_numpy().mean())
                if selected_columns
                else 0.0
            ),
            complete_row_rate=float(output.notna().all(axis=1).mean()),
            per_column_rate=per_column_rate,
            slopes={str(column): 0.0 for column in selected_columns},
            intercepts={str(column): -40.0 for column in selected_columns},
            drivers={str(column): str(column) for column in selected_columns},
            score_definitions={str(column): "complete" for column in selected_columns},
        )
        metadata = {
            "calibration": "population_fixed",
            "quadratic_a": None,
            "expected_missing_rate": 0.0,
        }
        return output, diagnostics, metadata

    if population_mean is None or population_std is None:
        raise ValueError(
            "population_mean and population_std are required for population-calibrated masks"
        )

    intercepts: dict[str, float] = {}
    slopes = {str(column): float(slope) for column in selected_columns}
    score_definitions: dict[str, str] = {}
    drivers = {str(column): str(column) for column in selected_columns}

    # Draw mask uniforms row-major in one matrix. With the same seed and column
    # order, an n1-row run is exactly the observed-data prefix of an n2-row run
    # whenever n1 <= n2 and the underlying raw SEM sample is prefix-coupled.
    uniforms = rng.random((len(data), len(selected_columns)))
    metadata = {
        "calibration": "population_fixed",
        "expected_missing_rate": float(target_rate),
        "quadratic_a": None,
        "quadratic_c": None,
    }

    if mode == "self_masking_logistic_population":
        intercept = calibrate_population_logistic_intercept(
            float(target_rate),
            float(slope),
        )
        for column_index, column in enumerate(selected_columns):
            column = str(column)
            mean = float(population_mean[column])
            std = float(population_std[column])
            if not np.isfinite(std) or std <= 0:
                raise ValueError(f"bad population std for {column}: {std}")

            standardized = (data[column].to_numpy(dtype=float) - mean) / std
            probabilities = _logistic(float(slope) * standardized + intercept)
            output.loc[uniforms[:, column_index] < probabilities, column] = np.nan
            intercepts[column] = float(intercept)
            score_definitions[column] = f"population_z({column})"
    else:
        target_retention = 1.0 - float(target_rate)
        coefficient = choose_quadratic_a(target_retention, float(quadratic_a))
        retention_constant = target_retention * np.sqrt(1.0 + coefficient)
        if retention_constant > 1.0 + 1e-12:
            raise AssertionError("quadratic probability constant exceeded one")

        for column_index, column in enumerate(selected_columns):
            column = str(column)
            mean = float(population_mean[column])
            std = float(population_std[column])
            standardized = (data[column].to_numpy(dtype=float) - mean) / std
            retention_probability = np.clip(
                retention_constant * np.exp(-0.5 * coefficient * standardized * standardized),
                0.0,
                1.0,
            )
            output.loc[
                uniforms[:, column_index] >= retention_probability,
                column,
            ] = np.nan
            intercepts[column] = float(np.log(retention_constant))
            slopes[column] = float(coefficient)
            score_definitions[column] = (
                f"c*exp(-a*population_z({column})^2/2)"
            )

        metadata.update(
            {
                "quadratic_a": float(coefficient),
                "quadratic_c": float(retention_constant),
            }
        )

    per_column_rate = {
        str(column): float(output[column].isna().mean()) for column in output.columns
    }
    diagnostics = MissingnessDiagnostics(
        mode=mode,
        target_rate=float(target_rate),
        realized_cell_rate=float(output.isna().to_numpy().mean()),
        realized_masked_cell_rate=(
            float(output.loc[:, selected_columns].isna().to_numpy().mean())
            if selected_columns
            else 0.0
        ),
        complete_row_rate=float(output.notna().all(axis=1).mean()),
        per_column_rate=per_column_rate,
        slopes=slopes,
        intercepts=intercepts,
        drivers=drivers,
        score_definitions=score_definitions,
    )
    return output, diagnostics, metadata
