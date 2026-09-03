"""Regression tests for deterministic shard merging and integrity checks."""
from pathlib import Path
import sys
import pytest

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'code'))
from scripts.merge_shards import validate_shard_contract


def _cfg(index, n=2):
    return {
        'config': {'x': 1}, 'execution_mode': 'full', 'trace_mode': 'summary',
        'num_shards': n, 'shard_index': index, 'max_cells': None,
    }


def test_merge_accepts_complete_distinct_shard_indices():
    common, indices=validate_shard_contract([_cfg(0),_cfg(1)],[Path('a'),Path('b')])
    assert indices==[0,1]
    assert common['num_shards']==2
    assert 'shard_index' not in common


def test_merge_rejects_duplicate_or_incomplete_shards():
    with pytest.raises(ValueError):
        validate_shard_contract([_cfg(0),_cfg(0)],[Path('a'),Path('b')])
    with pytest.raises(ValueError):
        validate_shard_contract([_cfg(0,4),_cfg(1,4)],[Path('a'),Path('b')])
