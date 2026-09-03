"""Regression tests for deterministic, scientifically transparent experiment-cell identities."""
from pathlib import Path
import sys,yaml
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'code'))
from experiments.run_recovery_experiments import expand_specs, scientific_topology_entry


def test_execution_only_topology_limits_do_not_change_scientific_identity():
    a={'name':'rr','enum':'random_regular','params':{'degree':2},'max_p':150}
    b={'name':'rr','enum':'random_regular','params':{'degree':2}}
    assert scientific_topology_entry(a)==scientific_topology_entry(b)


def test_registered_cross_block_anchor_counts_are_expected():
    def ids(name):
        cfg=yaml.safe_load((ROOT/'configs'/name).read_text())
        return {x['cell_id'] for x in expand_specs(cfg)}
    primary=ids('primary_scaling.yaml')
    alpha=ids('significance_threshold_sensitivity.yaml')
    retention=ids('retention_sensitivity.yaml')
    assert len(primary & alpha)==180
    assert len(primary & retention)==40
    assert len(alpha & retention)==40
