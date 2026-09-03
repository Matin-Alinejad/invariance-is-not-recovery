"""Explicit missingness mechanisms used by the rigorous experiment suite.

The functions here avoid global NumPy RNG state, calibrate logistic intercepts by
bisection, and return diagnostics.  They distinguish coordinate-wise
self-masking from cross-variable non-self-masking instead of hiding both behind
a generic MNAR label.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Dict, Mapping, Optional, Sequence

import numpy as np
import pandas as pd


@dataclass(frozen=True)
class MissingnessDiagnostics:
    """Summary of the configured and realized missingness mechanism."""
    mode: str
    target_rate: float
    realized_cell_rate: float
    realized_masked_cell_rate: float
    complete_row_rate: float
    per_column_rate: Dict[str, float]
    slopes: Dict[str, float]
    intercepts: Dict[str, float]
    drivers: Dict[str, str]
    score_definitions: Dict[str, str]


def _logistic(x: np.ndarray) -> np.ndarray:
    x = np.clip(np.asarray(x, dtype=float), -40.0, 40.0)
    return 1.0 / (1.0 + np.exp(-x))


def _zscore(x: np.ndarray) -> np.ndarray:
    x = np.asarray(x, dtype=float)
    finite = np.isfinite(x)
    out = np.zeros_like(x, dtype=float)
    if not finite.any():
        return out
    mean = float(np.mean(x[finite]))
    std = float(np.std(x[finite]))
    if std <= 1e-12:
        out[finite] = 0.0
    else:
        out[finite] = (x[finite] - mean) / std
    out[~finite] = 0.0
    return out


def calibrate_logistic_intercept(score: np.ndarray, target_rate: float, slope: float) -> float:
    """Return b such that mean(sigmoid(slope*score+b)) approximately target_rate."""
    if not 0.0 <= target_rate <= 1.0:
        raise ValueError("target_rate must lie in [0,1]")
    if target_rate == 0.0:
        return -40.0
    if target_rate == 1.0:
        return 40.0
    score = np.asarray(score, dtype=float)
    lo, hi = -40.0, 40.0
    for _ in range(100):
        mid = (lo + hi) / 2.0
        rate = float(_logistic(slope * score + mid).mean())
        if rate < target_rate:
            lo = mid
        else:
            hi = mid
    return (lo + hi) / 2.0


def inject_coordinate_missingness(
    data: pd.DataFrame,
    *,
    mode: str,
    target_rate: float,
    seed: int,
    columns: Optional[Sequence[str]] = None,
    slope: float | Mapping[str, float] = 1.0,
    driver_map: Optional[Mapping[str, str]] = None,
) -> tuple[pd.DataFrame, MissingnessDiagnostics]:
    """Inject calibrated coordinate-wise missingness.

    Parameters
    ----------
    mode:
        ``complete`` leaves data unchanged; ``self_masking`` makes missingness
        of column j depend only on its own value. ``nonself_masking`` is a
        deliberately non-separable stress mechanism: the logit for column j
        depends on the standardized sum of j and a different driver variable.
        This is useful as a negative-control selection mechanism; it is not
        presented as the only possible form of non-self-masking MNAR.
    columns:
        Columns to mask. Other columns remain fully observed.
    slope:
        Common logistic slope or per-column slopes. The intercept is calibrated
        separately for each column so the *expected* missingness rate matches
        ``target_rate``.
    """
    if mode not in {"complete", "self_masking", "nonself_masking"}:
        raise ValueError(f"Unknown missingness mode: {mode}")
    if not 0.0 <= target_rate < 1.0:
        raise ValueError("target_rate must lie in [0,1)")
    if mode == "complete" and target_rate != 0.0:
        raise ValueError("complete mode requires target_rate=0")

    out = data.copy()
    selected = list(columns) if columns is not None else list(data.columns)
    missing = [c for c in selected if c not in data.columns]
    if missing:
        raise KeyError(f"Unknown columns: {missing}")

    if mode == "complete" or target_rate == 0.0 or not selected:
        rates = {str(c): float(out[c].isna().mean()) for c in out.columns}
        diag = MissingnessDiagnostics(
            mode="complete",
            target_rate=float(target_rate),
            realized_cell_rate=float(out.isna().to_numpy().mean()),
            realized_masked_cell_rate=(
                float(out.loc[:, selected].isna().to_numpy().mean()) if selected else 0.0
            ),
            complete_row_rate=float(out.notna().all(axis=1).mean()),
            per_column_rate=rates,
            slopes={str(c): 0.0 for c in selected},
            intercepts={str(c): -40.0 for c in selected},
            drivers={str(c): str(c) for c in selected},
            score_definitions={str(c): "complete/no_added_mask" for c in selected},
        )
        return out, diag

    rng = np.random.default_rng(int(seed))
    if isinstance(slope, Mapping):
        slopes = {str(c): float(slope[c]) for c in selected}
    else:
        slopes = {str(c): float(slope) for c in selected}

    if mode == "self_masking":
        drivers = {str(c): str(c) for c in selected}
    else:
        all_columns = [str(c) for c in data.columns]
        if len(all_columns) < 2:
            raise ValueError("nonself_masking requires at least two data columns")
        if driver_map is None:
            drivers = {}
            for c in map(str, selected):
                start = all_columns.index(c)
                drivers[c] = next(
                    all_columns[(start + offset) % len(all_columns)]
                    for offset in range(1, len(all_columns) + 1)
                    if all_columns[(start + offset) % len(all_columns)] != c
                )
        else:
            drivers = {str(c): str(driver_map[c]) for c in selected}
        bad = {c: d for c, d in drivers.items() if d not in data.columns or d == c}
        if bad:
            raise KeyError(f"Invalid non-self missingness drivers (must exist and differ from target): {bad}")

    intercepts: Dict[str, float] = {}
    score_definitions: Dict[str, str] = {}
    for c in selected:
        c = str(c)
        driver = drivers[c]
        own_score = _zscore(data[c].to_numpy(dtype=float))
        if mode == "self_masking":
            score = own_score
            score_definitions[c] = f"z({c})"
        else:
            driver_score = _zscore(data[driver].to_numpy(dtype=float))
            score = (own_score + driver_score) / np.sqrt(2.0)
            score_definitions[c] = f"(z({c})+z({driver}))/sqrt(2)"
        b = calibrate_logistic_intercept(score, target_rate, slopes[c])
        intercepts[c] = float(b)
        probs = _logistic(slopes[c] * score + b)
        mask = rng.random(len(data)) < probs
        out.loc[mask, c] = np.nan

    rates = {str(c): float(out[c].isna().mean()) for c in out.columns}
    diag = MissingnessDiagnostics(
        mode=mode,
        target_rate=float(target_rate),
        realized_cell_rate=float(out.isna().to_numpy().mean()),
        realized_masked_cell_rate=(
            float(out.loc[:, selected].isna().to_numpy().mean()) if selected else 0.0
        ),
        complete_row_rate=float(out.notna().all(axis=1).mean()),
        per_column_rate=rates,
        slopes=slopes,
        intercepts=intercepts,
        drivers=drivers,
        score_definitions=score_definitions,
    )
    return out, diag
