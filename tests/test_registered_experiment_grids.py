"""Regression tests for the exact registered experiment grids."""
from pathlib import Path
import yaml

from experiments.run_recovery_experiments import calibrated_sample_size, expand_specs

ROOT = Path(__file__).resolve().parents[1]


def _count(name: str) -> int:
    cfg = yaml.safe_load((ROOT / 'configs' / name).read_text())
    specs = expand_specs(cfg, quick=False)
    assert len({s['cell_id'] for s in specs}) == len(specs)
    return len(specs)


def test_registered_experiment_grid_counts_are_fixed():
    assert _count('primary_scaling.yaml') == 1020
    assert _count('significance_threshold_sensitivity.yaml') == 360
    assert _count('retention_sensitivity.yaml') == 120
    assert _count('matched_local_global.yaml') == 240
    assert _count('primary_scaling_precision_extension.yaml') == 1020

    # The production integer schedule is part of the registered design.
    expected = {
        20: (1000, 796),
        50: (2500, 2500),
        75: (3750, 4151),
        100: (5000, 5947),
        150: (7500, 9871),
    }
    for p, (n_linear, n_superlinear) in expected.items():
        assert calibrated_sample_size(p, 1.0, 50, 50) == n_linear
        assert calibrated_sample_size(p, 1.25, 50, 50) == n_superlinear


def test_matched_local_grid_is_actual_dedicated_local_search():
    cfg = yaml.safe_load((ROOT / 'configs' / 'matched_local_global.yaml').read_text())
    assert cfg['base']['local_search_method'] == 'pc_simple_heuristic'
    assert cfg['p_grid'] == [20, 50]
    assert cfg['base']['targets_per_graph'] == 10


def test_retention_sensitivity_is_theorem_preserving_quadratic_only():
    cfg = yaml.safe_load((ROOT / 'configs' / 'retention_sensitivity.yaml').read_text())
    assert cfg['missingness_modes'] == ['self_masking_gaussian_preserving']
    assert cfg['missing_rates'] == [0.1, 0.3, 0.5]
    assert cfg['base']['mask_variables'] == 'all'
