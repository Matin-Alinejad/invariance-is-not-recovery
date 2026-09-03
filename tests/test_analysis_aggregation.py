"""Regression tests for graph-level aggregation and Monte Carlo precision analysis."""
import sys
from pathlib import Path
import pandas as pd

REPO_ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(REPO_ROOT/'code'))

from analysis.summarize_recovery_results import graph_level_frame
from analysis.evaluate_monte_carlo_precision import graph_level_f1


def _frame():
    # Two independent generated graphs, each with three target restrictions.
    rows=[]
    for seed,cell_id,vals in [(0,'g0',[0.2,0.4,0.6]),(1,'g1',[0.6,0.8,1.0])]:
        for val in vals:
            rows.append(dict(cell_id=cell_id,seed=seed,evaluation_scope='target_restriction',
                topology='er',p=20,gamma=1.0,missingness_mode='complete',
                alpha_schedule='n^-1/2',f1=val,precision=val,recall=val))
    return pd.DataFrame(rows)


def test_target_rows_are_collapsed_within_generated_graph_before_summary():
    out=graph_level_frame(_frame())
    assert len(out)==2
    assert sorted(out['f1'].round(12).tolist())==[0.4,0.8]


def test_precision_gate_uses_generated_graph_as_replication_unit():
    out=graph_level_f1(_frame())
    assert len(out)==2
    assert out['seed'].nunique()==2
    assert sorted(out['f1'].round(12).tolist())==[0.4,0.8]
