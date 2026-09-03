"""Regression tests for population-calibrated self-masking mechanisms."""
import sys
from pathlib import Path
import numpy as np
import pandas as pd

REPO_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO_ROOT / 'code'))

from src.algorithms.population_calibrated_missingness import (
    calibrate_population_logistic_intercept, inject_population_calibrated_missingness
)

def test_population_logistic_calibration():
    b=calibrate_population_logistic_intercept(0.3,1.0)
    rng=np.random.default_rng(123)
    z=rng.normal(size=300000)
    p=1/(1+np.exp(-(z+b)))
    assert abs(p.mean()-0.3)<0.004

def test_quadratic_mask_is_fixed_and_near_target():
    rng=np.random.default_rng(3)
    x=rng.normal(size=200000)
    df=pd.DataFrame({'X0':x})
    out,diag,extra=inject_population_calibrated_missingness(df,mode='self_masking_gaussian_preserving',target_rate=0.3,seed=9,columns=['X0'],population_mean={'X0':0.0},population_std={'X0':1.0},quadratic_a=0.2)
    assert abs(out['X0'].isna().mean()-0.3)<0.006
    assert extra['calibration']=='population_fixed'
    assert 0<extra['quadratic_c']<=1

def test_quadratic_mask_selected_variance_matches_gaussian_tilt():
    rng=np.random.default_rng(41)
    x=rng.normal(size=400000)
    df=pd.DataFrame({'X0':x})
    out,diag,extra=inject_population_calibrated_missingness(
        df,mode='self_masking_gaussian_preserving',target_rate=0.25,seed=17,
        columns=['X0'],population_mean={'X0':0.0},population_std={'X0':1.0},quadratic_a=0.3)
    observed=out['X0'].dropna().to_numpy()
    a=float(extra['quadratic_a'])
    expected_var=1.0/(1.0+a)
    assert abs(observed.var(ddof=1)-expected_var)<0.012
