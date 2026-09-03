"""Regression tests for selected-law alignment under quadratic self-masking."""
from __future__ import annotations

import numpy as np
import pandas as pd

from src.algorithms.population_calibrated_missingness import inject_population_calibrated_missingness
from src.data_generation.sem_diagnostics import quadratic_selected_query_stats


def test_exact_selected_query_retention_and_partial_correlation_match_simulation():
    rng=np.random.default_rng(20260809)
    cov=np.array([[1.0,0.45,0.25],[0.45,1.4,0.35],[0.25,0.35,0.9]],dtype=float)
    n=500000
    x=rng.multivariate_normal(np.zeros(3),cov,size=n)
    df=pd.DataFrame(x,columns=['X0','X1','X2'])
    pop_std={f'X{i}':float(np.sqrt(cov[i,i])) for i in range(3)}
    observed,_,extra=inject_population_calibrated_missingness(
        df,mode='self_masking_gaussian_preserving',target_rate=0.30,seed=917,
        columns=['X0','X1','X2'],population_mean={'X0':0.0,'X1':0.0,'X2':0.0},
        population_std=pop_std,quadratic_a=0.2)
    rho_exact,ret_exact=quadratic_selected_query_stats(
        cov,[0,1,2],population_variances=np.diag(cov),masked_indices={0,1,2},
        quadratic_a=float(extra['quadratic_a']),quadratic_c=float(extra['quadratic_c']))
    kept=observed.dropna().to_numpy()
    ret_emp=len(kept)/n
    # Partial correlation via the inverse selected sample covariance.
    pcov=np.linalg.inv(np.cov(kept,rowvar=False,ddof=0))
    rho_emp=-pcov[0,1]/np.sqrt(pcov[0,0]*pcov[1,1])
    assert abs(ret_emp-ret_exact)<0.004
    assert abs(rho_emp-rho_exact)<0.008
