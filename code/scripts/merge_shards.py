"""Merge non-overlapping experiment shard directories with integrity checks."""
from __future__ import annotations

import argparse
import json
import shutil
from pathlib import Path

import pandas as pd


def canonical_config(path: Path):
    """Return the scientific configuration after removing shard-specific execution fields."""
    if not path.exists():
        return None
    return json.loads(path.read_text())


def resolved_config_common(config: dict) -> dict:
    """Return the part that must agree across shards.

    ``shard_index`` is intentionally shard-specific.  Every other execution
    field, including ``num_shards`` and ``max_cells``, is part of the merge
    contract.
    """
    out = dict(config)
    out.pop("shard_index", None)
    return out


def validate_shard_contract(configs: list[dict | None], inputs: list[Path]) -> tuple[dict, list[int]]:
    """Validate that shard configurations agree scientifically and partition cells correctly."""
    if any(c is None for c in configs):
        missing = [str(inputs[i] / "resolved_config.json") for i, c in enumerate(configs) if c is None]
        raise ValueError(f"Missing shard resolved_config.json: {missing}")
    present = [c for c in configs if c is not None]
    common = resolved_config_common(present[0])
    if any(resolved_config_common(c) != common for c in present[1:]):
        raise ValueError("Shard resolved_config.json common contracts differ")
    num_shards = int(common.get("num_shards", 1))
    indices = [int(c.get("shard_index", -1)) for c in present]
    if len(indices) != len(set(indices)):
        raise ValueError(f"Duplicate shard indices: {indices}")
    expected = list(range(num_shards))
    if sorted(indices) != expected:
        raise ValueError(f"Incomplete shard set: observed {sorted(indices)}, expected {expected}")
    if len(inputs) != num_shards:
        raise ValueError(f"Expected {num_shards} shard directories, received {len(inputs)}")
    return common, sorted(indices)


def copy_tree_files(source: Path, destination: Path) -> None:
    """Copy optional per-cell metadata or traces while rejecting path collisions."""
    if not source.exists():
        return
    destination.mkdir(parents=True, exist_ok=True)
    for path in source.rglob('*'):
        if not path.is_file():
            continue
        relative = path.relative_to(source)
        target = destination / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        if target.exists() and target.read_bytes() != path.read_bytes():
            raise ValueError(f'Conflicting artifact: {target}')
        if not target.exists():
            shutil.copy2(path, target)


def main() -> None:
    """Merge distributed shard outputs into one validated experiment result directory."""
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument('--input-dir', action='append', required=True)
    parser.add_argument('--output-dir', required=True)
    args = parser.parse_args()

    inputs = [Path(x).resolve() for x in args.input_dir]
    output = Path(args.output_dir).resolve()
    output.mkdir(parents=True, exist_ok=True)

    configs = [canonical_config(d / 'resolved_config.json') for d in inputs]
    common_config, shard_indices = validate_shard_contract(configs, inputs)

    frames = []
    seen: set[str] = set()
    for directory in inputs:
        result = directory / 'results.csv'
        if not result.exists():
            raise FileNotFoundError(result)
        frame = pd.read_csv(result, dtype={"cell_id": "string"})
        ids = set(frame['cell_id'].astype(str).unique())
        overlap = seen & ids
        if overlap:
            raise ValueError(f'Overlapping cell IDs across shards: {sorted(overlap)[:10]}')
        seen |= ids
        frame['_source_shard'] = directory.name
        frames.append(frame)


    merged = pd.concat(frames, ignore_index=True)
    merged.to_csv(output / 'results.csv', index=False)
    merged_config = dict(common_config)
    merged_config["shard_index"] = "merged"
    merged_config["input_shard_indices"] = shard_indices
    (output / 'resolved_config.json').write_text(json.dumps(merged_config, indent=2, sort_keys=True) + '\n')

    failures = []
    environments = {}
    for directory in inputs:
        failure = directory / 'failures.csv'
        if failure.exists():
            f = pd.read_csv(failure)
            f['_source_shard'] = directory.name
            failures.append(f)
        env = directory / 'environment.json'
        if env.exists():
            environments[directory.name] = json.loads(env.read_text())
        copy_tree_files(directory / 'metadata', output / 'metadata')
        copy_tree_files(directory / 'traces', output / 'traces')
    if failures:
        pd.concat(failures, ignore_index=True).to_csv(output / 'failures.csv', index=False)
    (output / 'shard_environments.json').write_text(json.dumps(environments, indent=2, sort_keys=True) + '\n')
    (output / 'merge_report.json').write_text(json.dumps({
        'input_dirs': [str(x) for x in inputs],
        'unique_cells': len(seen),
        'result_rows': len(merged),
        'failures': int(sum(len(x) for x in failures)),
    }, indent=2) + '\n')
    print(f'Merged {len(inputs)} shards, {len(seen)} unique cells -> {output}')


if __name__ == '__main__':
    main()
