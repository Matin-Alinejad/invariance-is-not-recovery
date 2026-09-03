"""Regression tests for the registered all-variable masking scope."""
from pathlib import Path
import yaml

ROOT=Path(__file__).resolve().parents[1]


def test_all_registered_configs_mask_all_query_coordinates():
    for path in sorted((ROOT/'configs').glob('*.yaml')):
        cfg=yaml.safe_load(path.read_text())
        assert cfg['base']['mask_variables']=='all', path.name
