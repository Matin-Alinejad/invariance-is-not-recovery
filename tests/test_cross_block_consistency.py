"""Regression tests for scientific consistency across registered experiment blocks."""
import importlib.util
from pathlib import Path
import pandas as pd

SPEC=importlib.util.spec_from_file_location('anchor_audit', Path('code/scripts/verify_cross_block_consistency.py'))
mod=importlib.util.module_from_spec(SPEC); SPEC.loader.exec_module(mod)

def _frame(v):
    return pd.DataFrame({'cell_id':['c1'],'evaluation_scope':['global_whole_skeleton'],'target':[''], 'metric':[v], 'runtime_seconds':[1.0]})

def test_machine_roundoff_is_not_a_reproducibility_failure():
    out=mod.compare_pair('a',_frame(1.0),'b',_frame(1.0+5e-14))
    assert out['pass']

def test_material_numeric_drift_is_detected():
    out=mod.compare_pair('a',_frame(1.0),'b',_frame(1.0+1e-6))
    assert not out['pass']
