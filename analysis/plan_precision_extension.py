"""Pilot-based seed-count planning from Monte Carlo precision targets."""
from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any, Dict, List

import numpy as np
import pandas as pd
from scipy.stats import norm


def required_n_for_mean(sd: float, half_width: float, confidence: float) -> int:
    """Estimate the normal-approximation seed count required for a target mean half-width."""
    if not np.isfinite(sd) or sd < 0 or half_width <= 0 or not 0 < confidence < 1:
        return 0
    z = float(norm.ppf(0.5 + confidence / 2.0))
    return max(2, int(math.ceil((z * sd / half_width) ** 2)))


def main() -> None:
    """Create a precision-extension planning table from pilot seed-level variation."""
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--input", required=True, help="Graph results.csv")
    parser.add_argument("--output-dir", required=True)
    parser.add_argument("--metric", default="f1")
    parser.add_argument("--half-width", type=float, default=0.03)
    parser.add_argument("--confidence", type=float, default=0.95)
    args = parser.parse_args()
    frame = pd.read_csv(args.input)
    out = Path(args.output_dir)
    out.mkdir(parents=True, exist_ok=True)
    metric = args.metric
    required = {"cell_id", "seed", "p", "evaluation_scope", metric}
    missing = required - set(frame.columns)
    if missing:
        raise ValueError(f"Missing columns: {sorted(missing)}")

    condition_cols = [c for c in [
        "evaluation_scope", "p", "topology", "sem_model", "missingness_mode",
        "missing_rate_target", "alpha_schedule", "ci_test", "d_alg",
        "local_search_method",
    ] if c in frame.columns]
    seed_level = frame.groupby(condition_cols + ["seed"], as_index=False, dropna=False)[metric].mean()
    rows: List[Dict[str, Any]] = []
    for keys, sub in seed_level.groupby(condition_cols, dropna=False):
        values = sub[metric].dropna().to_numpy(float)
        key_tuple = keys if isinstance(keys, tuple) else (keys,)
        sd = float(values.std(ddof=1)) if len(values) > 1 else np.nan
        n_req = required_n_for_mean(sd, args.half_width, args.confidence)
        rows.append({
            **dict(zip(condition_cols, key_tuple)),
            "metric": metric,
            "pilot_n_seeds": int(len(values)),
            "pilot_mean": float(values.mean()) if len(values) else np.nan,
            "pilot_sd_across_seeds": sd,
            "target_ci_half_width": float(args.half_width),
            "confidence": float(args.confidence),
            "normal_approx_required_seeds": int(n_req),
            "additional_seeds_needed": int(max(0, n_req - len(values))),
            "warning": "Normal-approximation planning from pilot variance; re-evaluate after the first fixed seed block and retain the prespecified maximum.",
        })
    result = pd.DataFrame(rows)
    result.to_csv(out / "seed_precision_plan.csv", index=False)
    audit = {
        "metric": metric,
        "conditions": int(len(result)),
        "maximum_required_seeds": int(result["normal_approx_required_seeds"].max()) if len(result) else 0,
        "target_half_width": args.half_width,
        "confidence": args.confidence,
    }
    (out / "seed_precision_plan_audit.json").write_text(json.dumps(audit, indent=2) + "\n")
    print(f"Seed precision plan written to {out}")


if __name__ == "__main__":
    main()
