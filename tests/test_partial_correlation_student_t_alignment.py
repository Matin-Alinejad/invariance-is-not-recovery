"""Regression tests for partial-correlation Student-t calculations."""
from __future__ import annotations

import numpy as np
from scipy.stats import t as student_t
from sklearn.linear_model import LinearRegression

from src.algorithms.causal_discovery import TestWiseDeletionPC as _TestWiseDeletionPC


def test_conditional_pearson_uses_exact_residual_t_df_m_minus_s_minus_2():
    rng = np.random.default_rng(20260809)
    m, s = 300, 3
    z = rng.normal(size=(m, s))
    x = z @ np.array([0.7, -0.2, 0.4]) + rng.normal(size=m)
    y = z @ np.array([-0.3, 0.5, 0.1]) + 0.25 * x + rng.normal(size=m)
    alpha = 0.03
    alg = _TestWiseDeletionPC(alpha=alpha, ci_test='pearson')
    indep, p = alg.pc_algorithm.independence_test(x, y, z, min_samples=10)

    rx = x - LinearRegression().fit(z, x).predict(z)
    ry = y - LinearRegression().fit(z, y).predict(z)
    r = float(np.corrcoef(rx, ry)[0, 1])
    df = m - s - 2
    stat = abs(r) * np.sqrt(df / (1.0 - r * r))
    expected = float(2.0 * student_t.sf(stat, df=df))
    assert np.isclose(p, expected, rtol=1e-12, atol=1e-14)
    assert indep == (expected > alpha)


def test_unconditional_pearson_matches_student_t_df_m_minus_2():
    rng=np.random.default_rng(20260810)
    m=250
    x=rng.normal(size=m)
    y=0.2*x+rng.normal(size=m)
    alg=_TestWiseDeletionPC(alpha=0.04,ci_test='pearson')
    indep,p=alg.pc_algorithm.independence_test(x,y,None,min_samples=10)
    r=float(np.corrcoef(x,y)[0,1])
    df=m-2
    stat=abs(r)*np.sqrt(df/(1-r*r))
    expected=float(2.0*student_t.sf(stat,df=df))
    assert np.isclose(p,expected,rtol=1e-12,atol=1e-14)
    assert indep==(expected>0.04)
