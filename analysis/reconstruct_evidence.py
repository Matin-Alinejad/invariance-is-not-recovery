#!/usr/bin/env python3
"""Reconstruct the 25-file released evidence bundle from completed experiment outputs."""
from __future__ import annotations

import argparse
import shutil
from pathlib import Path

import pandas as pd

ROOT = Path(__file__).resolve().parents[1]

DEPTH_COLUMNS = [
    "topology",
    "p",
    "seed",
    "d_alg",
    "true_edges",
    "oracle_nonedges",
    "oracle_nonedges_separator_within_d_alg",
    "oracle_nonedges_unresolved_at_d_alg",
    "oracle_nonedges_unresolved_at_d_alg_lower_bound",
    "oracle_separator_coverage_fraction",
    "oracle_separator_depth_max_found",
    "oracle_separator_depth_mean_found",
    "oracle_separator_candidate_sets_tested",
    "oracle_depth_minimal_separator_calls",
    "oracle_depth_pairs_checked",
    "oracle_depth_audit_mode",
    "oracle_depth_failure_witness_x",
    "oracle_depth_failure_witness_y",
    "oracle_search_depth_premise_satisfied",
]

# Destination path in the released evidence tree -> source path in results/.
COPY_MAP = {
    "primary_scaling_10_seeds/analysis/data_quality_checks.json":
        "primary_scaling/analysis/data_quality_checks.json",
    "primary_scaling_10_seeds/analysis/paired_contrasts.csv":
        "primary_scaling/analysis/paired_contrasts.csv",
    "primary_scaling_10_seeds/analysis/monte_carlo_precision.csv":
        "primary_scaling/analysis/monte_carlo_precision.csv",
    "primary_scaling_10_seeds/analysis/summary.csv":
        "primary_scaling/analysis/summary.csv",
    "primary_scaling_20_seeds/analysis/data_quality_checks.json":
        "primary_scaling_20_seeds/analysis/data_quality_checks.json",
    "primary_scaling_20_seeds/analysis/paired_contrasts_20_seeds_descriptive.csv":
        "primary_scaling_20_seeds/analysis/paired_contrasts_20_seeds_descriptive.csv",
    "primary_scaling_20_seeds/analysis/monte_carlo_precision.csv":
        "primary_scaling_20_seeds/analysis/monte_carlo_precision.csv",
    "primary_scaling_20_seeds/analysis/summary.csv":
        "primary_scaling_20_seeds/analysis/summary.csv",
    "significance_threshold_sensitivity/analysis/data_quality_checks.json":
        "significance_threshold_sensitivity/analysis/data_quality_checks.json",
    "significance_threshold_sensitivity/analysis/paired_contrasts.csv":
        "significance_threshold_sensitivity/analysis/paired_contrasts.csv",
    "significance_threshold_sensitivity/analysis/monte_carlo_precision.csv":
        "significance_threshold_sensitivity/analysis/monte_carlo_precision.csv",
    "significance_threshold_sensitivity/analysis/summary.csv":
        "significance_threshold_sensitivity/analysis/summary.csv",
    "retention_sensitivity/analysis/data_quality_checks.json":
        "retention_sensitivity/analysis/data_quality_checks.json",
    "retention_sensitivity/analysis/monte_carlo_precision.csv":
        "retention_sensitivity/analysis/monte_carlo_precision.csv",
    "retention_sensitivity/analysis/retention_paired_contrasts.csv":
        "retention_sensitivity/analysis/retention_paired_contrasts.csv",
    "retention_sensitivity/analysis/retention_summary.csv":
        "retention_sensitivity/analysis/retention_summary.csv",
    "retention_sensitivity/analysis/summary.csv":
        "retention_sensitivity/analysis/summary.csv",
    "matched_local_global/analysis/data_quality_checks.json":
        "matched_local_global/analysis/data_quality_checks.json",
    "matched_local_global/analysis/matched_local_global_paired.csv":
        "matched_local_global/analysis/matched_local_global_paired.csv",
    "matched_local_global/analysis/monte_carlo_precision.csv":
        "matched_local_global/analysis/monte_carlo_precision.csv",
    "matched_local_global/analysis/summary.csv":
        "matched_local_global/analysis/summary.csv",
}


def copy_required(source: Path, destination: Path) -> None:
    """Copy a required evidence file or fail loudly if the source is absent."""
    if not source.exists():
        raise FileNotFoundError(source)
    destination.parent.mkdir(parents=True, exist_ok=True)
    shutil.copy2(source, destination)


def precision_summary_row(
    block: str,
    gate: pd.DataFrame,
    fixed_design_block: bool,
    note: str,
) -> dict:
    """Summarize one experiment block for the evidence-level precision program table."""
    needs_more_seeds = gate["needs_more_seeds"].astype(bool)
    return {
        "block": block,
        "groups": int(len(gate)),
        "groups_over_005": int(needs_more_seeds.sum()),
        "max_f1_halfwidth95": float(gate["f1_halfwidth95"].max()),
        "fixed_design_block": bool(fixed_design_block),
        "note": note,
    }


def main() -> int:
    """Rebuild the complete processed evidence bundle from merged experiment outputs."""
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--results-root", default=str(ROOT / "results"))
    parser.add_argument("--diagnostics-dir", default=str(ROOT / "results" / "diagnostics"))
    parser.add_argument("--out", default=str(ROOT / "results" / "reproduced_evidence"))
    args = parser.parse_args()

    results_root = Path(args.results_root).resolve()
    diagnostics_dir = Path(args.diagnostics_dir).resolve()
    output_dir = Path(args.out).resolve()
    if output_dir.exists():
        shutil.rmtree(output_dir)
    output_dir.mkdir(parents=True)

    for destination_rel, source_rel in COPY_MAP.items():
        copy_required(results_root / source_rel, output_dir / destination_rel)

    # The full structural audit contains auxiliary columns. The released evidence
    # keeps the exact 19-column projection used by the released validation checks.
    depth = pd.read_csv(diagnostics_dir / "depth_scope.csv")
    missing = [column for column in DEPTH_COLUMNS if column not in depth.columns]
    if missing:
        raise KeyError(f"depth_scope missing columns: {missing}")
    depth[DEPTH_COLUMNS].to_csv(output_dir / "depth_scope.csv", index=False)

    for name in ["p20_oracle_queries.csv", "population_margins.csv"]:
        copy_required(diagnostics_dir / name, output_dir / name)

    primary_10 = pd.read_csv(
        output_dir / "primary_scaling_10_seeds/analysis/monte_carlo_precision.csv"
    )
    primary_20 = pd.read_csv(
        output_dir / "primary_scaling_20_seeds/analysis/monte_carlo_precision.csv"
    )
    threshold = pd.read_csv(
        output_dir / "significance_threshold_sensitivity/analysis/monte_carlo_precision.csv"
    )
    retention = pd.read_csv(
        output_dir / "retention_sensitivity/analysis/monte_carlo_precision.csv"
    )
    matched_local = pd.read_csv(
        output_dir / "matched_local_global/analysis/monte_carlo_precision.csv"
    )

    program = pd.DataFrame(
        [
            precision_summary_row(
                "primary_scaling_10_seeds",
                primary_10,
                True,
                "Triggered the prespecified uniform seeds 10–19 precision extension.",
            ),
            precision_summary_row(
                "primary_scaling_20_seeds",
                primary_20,
                False,
                "Descriptive precision-extension analysis; 0/204 groups remain above 0.05.",
            ),
            precision_summary_row(
                "significance_threshold_sensitivity",
                threshold,
                True,
                "No precision extension required.",
            ),
            precision_summary_row(
                "retention_sensitivity",
                retention,
                True,
                "No precision extension required.",
            ),
            precision_summary_row(
                "matched_local_global_absolute_f1",
                matched_local,
                True,
                (
                    "Five absolute-F1 groups exceed 0.05; the matched local-vs-global "
                    "comparison uses paired graph-level contrasts rather than this absolute-F1 gate."
                ),
            ),
        ]
    )
    program.to_csv(output_dir / "experiment_program_summary.csv", index=False)

    evidence_files = sorted(path for path in output_dir.rglob("*") if path.is_file())
    if len(evidence_files) != 25:
        raise RuntimeError(f"Expected 25 evidence files, found {len(evidence_files)}")
    print(f"EVIDENCE BUNDLE: PASS ({len(evidence_files)} files) -> {output_dir}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
