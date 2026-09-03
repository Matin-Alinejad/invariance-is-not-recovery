"""Regression tests for separator-depth diagnostics on generated graphs."""
import networkx as nx

from src.data_generation.sem_diagnostics import pc_separator_depth_diagnostics


def _two_parallel_chains() -> nx.DiGraph:
    # X -> A -> Y and X -> B -> Y.  X and Y are nonadjacent and require
    # conditioning on both A and B; no size-0/1 separator exists.
    g = nx.DiGraph()
    g.add_edges_from([("X", "A"), ("A", "Y"), ("X", "B"), ("B", "Y")])
    return g


def test_depth_audit_returns_certified_failure_witness_without_fake_coverage():
    out = pc_separator_depth_diagnostics(_two_parallel_chains(), 1)
    assert out["oracle_search_depth_premise_satisfied"] is False
    assert out["oracle_depth_audit_mode"] == "early_exit_failure_witness"
    assert out["oracle_nonedges_unresolved_at_d_alg_lower_bound"] == 1
    assert out["oracle_separator_coverage_fraction"] != out["oracle_separator_coverage_fraction"]  # NaN
    x, y = out["oracle_depth_failure_witness_x"], out["oracle_depth_failure_witness_y"]
    assert {x, y} == {"X", "Y"}


def test_depth_audit_exhaustive_pass_when_depth_is_sufficient():
    out = pc_separator_depth_diagnostics(_two_parallel_chains(), 2)
    assert out["oracle_search_depth_premise_satisfied"] is True
    assert out["oracle_depth_audit_mode"] == "exhaustive_pass"
    assert out["oracle_nonedges_unresolved_at_d_alg"] == 0
    assert out["oracle_separator_coverage_fraction"] == 1.0
