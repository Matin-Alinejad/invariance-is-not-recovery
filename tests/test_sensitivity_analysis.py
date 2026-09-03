"""Regression tests for threshold and retention sensitivity analyses."""
from pathlib import Path
import sys
import pandas as pd

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'code'))
from analysis.compute_retention_and_local_contrasts import analyze_local, analyze_retention


def test_local_pairs_targets_before_graph_uncertainty():
    rows=[]
    for seed in [0,1]:
        for target in ['X0','X1']:
            base=dict(cell_id=f'c{seed}',topology='rr',p=20,gamma=1.0,missingness_mode='complete',missing_rate_target=0.0,alpha_schedule='n_inverse_half',seed=seed,target=target,cell_status='complete')
            rows.append({**base,'evaluation_scope':'target_restriction_of_global','f1':0.8,'precision':0.8,'recall':0.8,'exact_recovery':0,'fp':1,'fn':1,'trace_ci_tests':100,'runtime_seconds':1.0})
            rows.append({**base,'evaluation_scope':'dedicated_local','f1':0.9,'precision':0.9,'recall':0.9,'exact_recovery':1,'fp':0,'fn':0,'trace_ci_tests':20,'runtime_seconds':0.2})
    out=analyze_local(pd.DataFrame(rows))
    assert len(out)==1
    assert out.loc[0,'n_graph_seeds']==2
    assert abs(out.loc[0,'f1_delta_local_minus_global_mean']-0.1)<1e-12
    assert abs(out.loc[0,'ci_saving_fraction_mean']-0.8)<1e-12


def test_retention_rates_are_not_collapsed():
    rows=[]
    for seed in [0,1]:
        for rate,f1 in [(0.1,0.9),(0.3,0.8),(0.5,0.6)]:
            rows.append(dict(cell_id=f'c{seed}_{rate}',evaluation_scope='global_whole_skeleton',topology='rr',p=50,gamma=1.0,missingness_mode='self_masking_gaussian_preserving',missing_rate_target=rate,alpha_schedule='n_inverse_half',seed=seed,f1=f1,precision=f1,recall=f1,exact_recovery=0,fp=1,fn=1,trace_ci_tests=100,trace_ci_n_eff_min=100*(1-rate),trace_ci_n_eff_median=110*(1-rate),trace_ci_effective_fraction_mean=1-rate,runtime_seconds=1,missing_rate_realized_masked_cells=rate,complete_row_rate=1-rate,selected_edge_partial_corr_min=.1,selected_edge_query_retention_min=.2))
    desc,con=analyze_retention(pd.DataFrame(rows))
    assert set(desc.missing_rate_target)=={0.1,0.3,0.5}
    x=con[(con.rate_low==0.1)&(con.rate_high==0.5)]
    assert len(x)==1
    assert abs(x.iloc[0].f1_delta_mean+0.3)<1e-12


def test_local_reports_batch_target_cost_without_double_counting_global_fit():
    rows=[]
    for seed in [0,1]:
        for target in ['X0','X1']:
            base=dict(cell_id=f'c{seed}',topology='rr',p=20,gamma=1.0,missingness_mode='complete',missing_rate_target=0.0,alpha_schedule='n_inverse_half',seed=seed,target=target,cell_status='complete')
            rows.append({**base,'evaluation_scope':'target_restriction_of_global','f1':0.8,'precision':0.8,'recall':0.8,'exact_recovery':0,'fp':1,'fn':1,'trace_ci_tests':100,'runtime_seconds':1.0})
            rows.append({**base,'evaluation_scope':'dedicated_local','f1':0.9,'precision':0.9,'recall':0.9,'exact_recovery':1,'fp':0,'fn':0,'trace_ci_tests':30,'runtime_seconds':0.3})
    out=analyze_local(pd.DataFrame(rows))
    assert len(out)==1
    # Per target, local uses 30% of the global fit: 70% saving.
    assert abs(out.loc[0,'ci_saving_fraction_mean']-0.7)<1e-12
    # For both requested targets together, local uses 60 tests vs one global 100.
    assert abs(out.loc[0,'trace_ci_tests_dedicated_local_batch_total_mean']-60.0)<1e-12
    assert abs(out.loc[0,'trace_ci_tests_global_once_mean']-100.0)<1e-12
    assert abs(out.loc[0,'ci_saving_fraction_batch_targets_mean']-0.4)<1e-12
    assert abs(out.loc[0,'runtime_saving_fraction_batch_targets_mean']-0.4)<1e-12
