"""Utilities for deterministic, resumable experiment execution.

These helpers contain only execution bookkeeping. They do not alter the
scientific design, generated data, missingness mechanisms, CI tests, or metrics.
"""
from __future__ import annotations

import json
import os
import platform
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Iterable, Mapping, Sequence

import numpy as np
import pandas as pd


def canonical_json(value: Any) -> str:
    """Serialize a value deterministically for execution-contract checks."""
    return json.dumps(value, sort_keys=True, separators=(",", ":"), default=str)


def _flatten_mapping(value: Any, prefix: str = "") -> list[tuple[str, str]]:
    """Flatten nested scientific settings into stable, human-readable pairs."""
    out: list[tuple[str, str]] = []
    if isinstance(value, Mapping):
        for key in sorted(value):
            child = f"{prefix}.{key}" if prefix else str(key)
            out.extend(_flatten_mapping(value[key], child))
    elif isinstance(value, (list, tuple)):
        out.append((prefix, "-".join(str(x) for x in value)))
    else:
        out.append((prefix, str(value)))
    return out


def _slug(text: str) -> str:
    """Convert a setting token to a portable CSV-safe identifier fragment."""
    cleaned = []
    for ch in str(text):
        if ch.isalnum() or ch in {"-", "."}:
            cleaned.append(ch)
        else:
            cleaned.append("-")
    token = "".join(cleaned)
    while "--" in token:
        token = token.replace("--", "-")
    return token.strip("-") or "none"


def _compact_number(value: Any) -> str:
    """Format numeric settings compactly without losing registered precision."""
    if isinstance(value, bool):
        return str(value).lower()
    if isinstance(value, (int, np.integer)):
        return str(int(value))
    if isinstance(value, (float, np.floating)):
        return format(float(value), ".12g")
    return str(value)


def cell_id_from_mapping(mapping: Mapping[str, Any]) -> str:
    """Return a compact, deterministic, human-readable graph-cell identifier.

    The identifier uses the scientific factors that vary across the registered
    study. Abbreviations are documented here and keep metadata filenames
    portable while preserving cross-block identity for shared conditions.
    """
    topology = {
        "random_regular_d2": "rr2",
        "er_expected_degree_2": "er2",
        "small_world_k2": "sw2",
        "scale_free_m2": "sf2",
    }.get(str(mapping.get("topology_name")), _slug(mapping.get("topology_name", "top"))[:18])
    missingness = {
        "complete": "complete",
        "self_masking_gaussian_preserving": "quadratic",
        "self_masking_logistic_population": "logistic",
    }.get(str(mapping.get("missingness_mode")), _slug(mapping.get("missingness_mode", "miss"))[:18])
    alpha = {
        "fixed_005": "fixed005",
        "n_inverse_half": "ninvhalf",
        "n_inverse": "ninv",
        "bonferroni_pairs": "bonfpairs",
        "bonferroni_pc_upper": "bonfpc",
    }.get(str(mapping.get("alpha_schedule")), _slug(mapping.get("alpha_schedule", "alpha"))[:18])
    local = {
        "none": "none",
        "pc_simple_heuristic": "targetpc",
        "bounded_separator_exhaustive": "boundedsep",
    }.get(str(mapping.get("local_search_method")), _slug(mapping.get("local_search_method", "local"))[:18])
    parts = [
        f"p{_compact_number(mapping.get('p'))}",
        f"g{_compact_number(mapping.get('gamma'))}",
        f"top-{topology}",
        f"miss-{missingness}",
        f"r{_compact_number(mapping.get('missing_rate'))}",
        f"alpha-{alpha}",
        f"ci-{_slug(mapping.get('ci_test', 'ci'))[:10]}",
        f"d{_compact_number(mapping.get('max_conditioning_set_size'))}",
        f"local-{local}",
        f"targets{_compact_number(mapping.get('targets_per_graph'))}",
        f"seed{_compact_number(mapping.get('seed'))}",
    ]
    return "cell_" + "__".join(parts)


def atomic_write_json(path: Path, payload: Mapping[str, Any]) -> None:
    """Write JSON atomically so interrupted jobs do not leave partial files."""
    path.parent.mkdir(parents=True, exist_ok=True)
    temp = path.with_suffix(path.suffix + ".tmp")
    temp.write_text(json.dumps(payload, indent=2, sort_keys=True, default=str) + "\n")
    temp.replace(path)


def append_csv(path: Path, rows: Iterable[Mapping[str, Any]]) -> int:
    """Append result rows while preserving the initial CSV header."""
    rows = list(rows)
    if not rows:
        return 0
    frame = pd.DataFrame(rows)
    path.parent.mkdir(parents=True, exist_ok=True)
    frame.to_csv(path, mode="a", index=False, header=not path.exists())
    return len(frame)


def completed_cell_ids(path: Path, status_col: str = "cell_status") -> set[str]:
    """Read completed graph-cell identifiers from a resumable result CSV."""
    if not path.exists():
        return set()
    try:
        frame = pd.read_csv(path, usecols=lambda c: c in {"cell_id", status_col})
    except Exception:
        frame = pd.read_csv(path)
    if "cell_id" not in frame:
        return set()
    if status_col in frame:
        frame = frame[frame[status_col].fillna("complete") == "complete"]
    return set(frame["cell_id"].dropna().astype(str))


def assert_json_compatible(path: Path, payload: Mapping[str, Any]) -> None:
    """Refuse to resume into a directory with a different execution contract."""
    path = Path(path)
    if not path.exists():
        return
    try:
        existing = json.loads(path.read_text())
    except Exception as exc:
        raise ValueError(f"Cannot read existing execution specification {path}") from exc
    if canonical_json(existing) != canonical_json(payload):
        raise ValueError(
            f"Existing execution specification {path} differs from this run. "
            "Use a new output directory or --fresh."
        )


def package_versions(names: Sequence[str]) -> dict[str, str]:
    """Record installed package versions for cross-shard environment checks."""
    versions: dict[str, str] = {}
    try:
        from importlib.metadata import version
    except ImportError:  # pragma: no cover
        return versions
    for name in names:
        try:
            versions[name] = version(name)
        except Exception:
            versions[name] = "not-installed"
    return versions


def git_revision(repo_root: Path) -> str:
    """Record the repository revision when Git metadata is available."""
    try:
        return subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=repo_root, text=True, stderr=subprocess.DEVNULL
        ).strip()
    except Exception:
        return "unavailable"


def environment_manifest(repo_root: Path, command: Sequence[str]) -> dict[str, Any]:
    """Capture reproducibility-relevant software and hardware metadata."""
    return {
        "created_utc": datetime.now(timezone.utc).isoformat(),
        "command": list(command),
        "python": sys.version,
        "executable": sys.executable,
        "platform": platform.platform(),
        "processor": platform.processor(),
        "cpu_count": os.cpu_count(),
        "numpy_config": {"version": np.__version__},
        "packages": package_versions(
            [
                "numpy", "pandas", "scipy", "scikit-learn", "networkx",
                "matplotlib", "joblib", "pyyaml", "pytest", "statsmodels",
                "threadpoolctl",
            ]
        ),
        "git_revision": git_revision(repo_root),
    }
