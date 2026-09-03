"""Deterministic, instrumented test-wise-deletion PC skeleton search.

Scientific scope
----------------
This module instruments the test-wise-deletion PC skeleton search used by the
experiments. Each conditional-independence query uses its own complete-case set.
The implementation does not add missingness-graph corrections outside the study's
computational design.

The implementation records every CI call, uses deterministic conditioning-set
ordering, and exposes enough diagnostics to audit the theory/experiment link:
number of tests, conditioning-set sizes, effective sample sizes, decisions,
p-values, and timing.
"""
from __future__ import annotations

from dataclasses import asdict, dataclass
from itertools import combinations
from typing import Dict, Iterable, List, Optional, Sequence, Set, Tuple
import time

import networkx as nx
import numpy as np
import pandas as pd

from .causal_discovery import TestWiseDeletionPC


@dataclass(frozen=True)
class CITraceRecord:
    """Immutable record for one conditional-independence decision."""
    test_id: int
    mode: str
    x: str
    y: str
    conditioning_set: Tuple[str, ...]
    conditioning_size: int
    n_total: int
    n_effective: int
    effective_fraction: float
    p_value: float
    independent: bool
    decision_reason: str
    elapsed_seconds: float


class InstrumentedTestWiseDeletionPC(TestWiseDeletionPC):
    """PC skeleton search with test-wise deletion and exact CI-call tracing.

    This class implements the registered search with two important safeguards: adjacency
    sets are frozen within each conditioning level (PC-stable), and global
    separators are searched from both endpoints.  All traversals are sorted,
    removing dependence on Python hash randomization.
    """

    algorithm_name = "test_wise_deletion_pc"

    def __init__(
        self,
        *args,
        min_effective_samples: int = 10,
        record_trace: bool = True,
        insufficient_policy: str = "keep_edge",
        **kwargs,
    ):
        super().__init__(*args, **kwargs)
        self.min_effective_samples = int(min_effective_samples)
        self.record_trace = bool(record_trace)
        self.insufficient_policy = str(insufficient_policy)
        if self.min_effective_samples < 3:
            raise ValueError("min_effective_samples must be at least 3")
        if self.insufficient_policy not in {"keep_edge", "prune_edge", "raise"}:
            raise ValueError("insufficient_policy must be keep_edge, prune_edge, or raise")
        self.trace: List[CITraceRecord] = []
        self.separation_sets: Dict[Tuple[str, str], Tuple[str, ...]] = {}
        self._summary_rows: List[Tuple[int, int, float, int, bool, str, float]] = []

    def reset_trace(self) -> None:
        self.trace = []
        self.separation_sets = {}
        self._summary_rows = []

    def trace_frame(self) -> pd.DataFrame:
        columns = [field.name for field in CITraceRecord.__dataclass_fields__.values()]
        if not self.trace:
            return pd.DataFrame(columns=columns)
        return pd.DataFrame([asdict(row) for row in self.trace], columns=columns)

    def trace_summary(self, mode_prefix: Optional[str] = None) -> Dict[str, float]:
        if mode_prefix is not None and self.record_trace:
            frame = self.trace_frame()
            if not frame.empty:
                frame = frame[frame["mode"].astype(str).str.startswith(mode_prefix)]
            rows = [
                (int(r.n_effective), int(r.conditioning_size), float(r.effective_fraction),
                 int(r.n_total), bool(r.independent), str(r.decision_reason),
                 float(r.elapsed_seconds))
                for r in self.trace
                if str(r.mode).startswith(mode_prefix)
            ]
        else:
            rows = self._summary_rows
        if not rows:
            return {
                "ci_tests": 0,
                "ci_n_eff_mean": np.nan,
                "ci_n_eff_median": np.nan,
                "ci_n_eff_min": np.nan,
                "ci_effective_fraction_mean": np.nan,
                "ci_cond_size_mean": np.nan,
                "ci_cond_size_max": np.nan,
                "ci_independent_fraction": np.nan,
                "ci_insufficient_fraction": np.nan,
                "ci_nonfinite_fraction": np.nan,
                "ci_insufficient_prune_fraction": np.nan,
                "ci_insufficient_keep_fraction": np.nan,
                "ci_elapsed_total": 0.0,
            }
        n_eff = np.asarray([r[0] for r in rows], dtype=float)
        cond = np.asarray([r[1] for r in rows], dtype=float)
        frac = np.asarray([r[2] for r in rows], dtype=float)
        indep = np.asarray([r[4] for r in rows], dtype=float)
        reasons = np.asarray([str(r[5]) for r in rows], dtype=object)
        insuff = reasons == "insufficient_effective_samples"
        nonfinite = reasons == "nonfinite_p_value"
        insuff_prune = insuff & np.asarray([bool(r[4]) for r in rows], dtype=bool)
        insuff_keep = insuff & ~np.asarray([bool(r[4]) for r in rows], dtype=bool)
        elapsed = np.asarray([r[6] for r in rows], dtype=float)
        return {
            "ci_tests": int(len(rows)),
            "ci_n_eff_mean": float(n_eff.mean()),
            "ci_n_eff_median": float(np.median(n_eff)),
            "ci_n_eff_min": int(n_eff.min()),
            "ci_effective_fraction_mean": float(frac.mean()),
            "ci_cond_size_mean": float(cond.mean()),
            "ci_cond_size_max": int(cond.max()),
            "ci_independent_fraction": float(indep.mean()),
            "ci_insufficient_fraction": float(insuff.mean()),
            "ci_nonfinite_fraction": float(nonfinite.mean()),
            "ci_insufficient_prune_fraction": float(insuff_prune.mean()),
            "ci_insufficient_keep_fraction": float(insuff_keep.mean()),
            "ci_elapsed_total": float(elapsed.sum()),
        }

    @staticmethod
    def _ordered_conditioning_sets(nodes: Iterable[str], size: int) -> Iterable[Tuple[str, ...]]:
        ordered = tuple(sorted(nodes))
        if size < 0 or size > len(ordered):
            return ()
        return combinations(ordered, size)

    def _run_named_ci(
        self,
        data: pd.DataFrame,
        x: str,
        y: str,
        conditioning_set: Sequence[str] | Set[str],
        mode: str,
    ) -> Tuple[bool, float]:
        z_names = tuple(sorted(conditioning_set))
        cols = [x, y, *z_names]
        n_total = int(len(data))
        complete_rows = data.loc[:, cols].replace([np.inf, -np.inf], np.nan).dropna()
        n_effective = int(len(complete_rows))
        effective_fraction = float(n_effective / n_total) if n_total else np.nan
        z_data: Optional[np.ndarray] = data.loc[:, list(z_names)].to_numpy() if z_names else None

        t0 = time.perf_counter()
        required_samples = max(self.min_effective_samples, len(z_names) + 3)
        if n_effective < required_samples:
            reason = "insufficient_effective_samples"
            if self.insufficient_policy == "raise":
                raise RuntimeError(
                    f"Only {n_effective} complete rows for CI({x},{y}|{z_names}); "
                    f"minimum is {required_samples}"
                )
            independent = self.insufficient_policy == "prune_edge"
            p_value = 1.0 if independent else 0.0
        else:
            x_clean = complete_rows[x].to_numpy(dtype=float)
            y_clean = complete_rows[y].to_numpy(dtype=float)
            z_clean = (
                complete_rows.loc[:, list(z_names)].to_numpy(dtype=float)
                if z_names else None
            )
            independent, p_value = self.pc_algorithm.independence_test(
                x_clean, y_clean, z_clean, min_samples=required_samples
            )
            reason = "nonfinite_p_value" if not np.isfinite(p_value) else "p_value_threshold"
        elapsed = time.perf_counter() - t0

        record = CITraceRecord(
            test_id=len(self._summary_rows),
            mode=mode,
            x=x,
            y=y,
            conditioning_set=z_names,
            conditioning_size=len(z_names),
            n_total=n_total,
            n_effective=n_effective,
            effective_fraction=effective_fraction,
            p_value=float(p_value),
            independent=bool(independent),
            decision_reason=reason,
            elapsed_seconds=float(elapsed),
        )
        self._summary_rows.append(
            (n_effective, len(z_names), effective_fraction, n_total,
             bool(independent), str(reason), float(elapsed))
        )
        if self.record_trace:
            self.trace.append(record)
        return bool(independent), float(p_value)

    @staticmethod
    def _two_sided_conditioning_sets(
        adj_x: Set[str], adj_y: Set[str], size: int
    ) -> Iterable[Tuple[str, ...]]:
        """Stable-PC conditioning sets from either endpoint, without duplicates.

        Testing only the lexicographically first endpoint can miss a valid
        separator that lies in the other endpoint's adjacency set.  The
        standard skeleton search permits either side.
        """
        candidates = {
            tuple(cond)
            for pool in (adj_x, adj_y)
            if len(pool) >= size
            for cond in combinations(tuple(sorted(pool)), size)
        }
        return iter(sorted(candidates))

    def find_adjacencies_with_missing(self, data: pd.DataFrame) -> nx.Graph:
        """Stable-PC skeleton search using test-wise complete cases.

        Adjacency sets are frozen at each conditioning level (PC-stable), and
        separators are searched from both endpoints.  Edges may be removed
        during the level, but those removals cannot change which conditioning
        sets are available to later edges at the same level.
        """
        variables = sorted(map(str, data.columns))
        graph = nx.Graph()
        graph.add_nodes_from(variables)
        graph.add_edges_from(combinations(variables, 2))

        level = 0
        while level <= self.max_conditioning_set_size:
            adjacency_snapshot = {node: set(graph.neighbors(node)) for node in variables}
            any_testable_edge = False
            for x, y in sorted(graph.edges()):
                if not graph.has_edge(x, y):
                    continue
                adj_x = adjacency_snapshot[x] - {y}
                adj_y = adjacency_snapshot[y] - {x}
                if max(len(adj_x), len(adj_y)) < level:
                    continue
                any_testable_edge = True
                for cond in self._two_sided_conditioning_sets(adj_x, adj_y, level):
                    independent, _ = self._run_named_ci(data, x, y, cond, mode="global")
                    if independent:
                        graph.remove_edge(x, y)
                        self.separation_sets[(x, y)] = tuple(cond)
                        self.separation_sets[(y, x)] = tuple(cond)
                        break
            if not any_testable_edge:
                break
            level += 1
        return graph

    def find_local_adjacencies_with_missing(self, data: pd.DataFrame, target: str) -> Set[str]:
        """Order-stable PC-simple-style target heuristic.

        Every CI call involves the target, and candidates are frozen within a
        conditioning level.  The conditioning pool is restricted to the
        target's current candidate set.  This is computationally attractive but
        is *not* a generally sound target-skeleton search for arbitrary faithful
        DAGs; ``code/scripts/oracle_search_audit.py`` contains explicit oracle
        counterexamples.  Keep this method only as a labelled heuristic.
        """
        variables = sorted(map(str, data.columns))
        if target not in variables:
            raise ValueError(f"Unknown target {target!r}")
        neighbors: Set[str] = {v for v in variables if v != target}

        for size in range(self.max_conditioning_set_size + 1):
            snapshot = set(neighbors)
            any_testable_candidate = False
            for x in sorted(snapshot):
                if x not in neighbors:
                    continue
                candidate_z = snapshot - {x}
                if len(candidate_z) < size:
                    continue
                any_testable_candidate = True
                for cond in self._ordered_conditioning_sets(candidate_z, size):
                    independent, _ = self._run_named_ci(
                        data, target, x, cond, mode=f"local:{target}"
                    )
                    if independent:
                        neighbors.discard(x)
                        self.separation_sets[(target, x)] = tuple(cond)
                        self.separation_sets[(x, target)] = tuple(cond)
                        break
            if not any_testable_candidate:
                break
        return neighbors


    def find_target_adjacencies_bounded_separator_with_missing(
        self, data: pd.DataFrame, target: str
    ) -> Set[str]:
        """Search all bounded-size separators for each target/candidate pair.

        Unlike :meth:`find_local_adjacencies_with_missing`, conditioning sets
        are drawn from all variables other than the tested pair.  With an oracle
        CI test this is sound whenever each non-neighbour admits a separator no
        larger than ``max_conditioning_set_size``.  Its combinatorial cost is
        high, so it is intended for small/medium-p validation and as a
        correctness benchmark.
        """
        variables = sorted(map(str, data.columns))
        if target not in variables:
            raise ValueError(f"Unknown target {target!r}")
        retained: Set[str] = set()
        for x in variables:
            if x == target:
                continue
            pool = [v for v in variables if v not in {target, x}]
            separated = False
            for size in range(min(self.max_conditioning_set_size, len(pool)) + 1):
                for cond in combinations(tuple(pool), size):
                    independent, _ = self._run_named_ci(
                        data, target, x, cond, mode=f"target_bounded_separator:{target}"
                    )
                    if independent:
                        separated = True
                        break
                if separated:
                    break
            if not separated:
                retained.add(x)
        return retained

    def fit_target_bounded_separator_with_trace(
        self, data: pd.DataFrame, target: str
    ) -> Tuple[nx.DiGraph, pd.DataFrame]:
        """Fit the bounded-separator target search and return its CI trace."""
        self.reset_trace()
        clean = data.copy()
        if np.any(np.isinf(clean.values)) or np.any(np.abs(clean.values) > 1e12):
            clean = clean.replace([np.inf, -np.inf], np.nan)
            clean = clean.clip(lower=-1e12, upper=1e12)
        adjacent = self.find_target_adjacencies_bounded_separator_with_missing(clean, target)
        graph = nx.DiGraph()
        graph.add_nodes_from(clean.columns)
        for x in adjacent:
            graph.add_edge(target, x)
            graph.add_edge(x, target)
        return graph, self.trace_frame().copy()

    def fit_with_trace(self, data: pd.DataFrame) -> Tuple[nx.DiGraph, pd.DataFrame]:
        self.reset_trace()
        graph = self.fit(data)
        return graph, self.trace_frame().copy()

    def fit_local_with_trace(
        self, data: pd.DataFrame, target: str
    ) -> Tuple[nx.DiGraph, pd.DataFrame]:
        self.reset_trace()
        graph = self.fit_local(data, target)
        return graph, self.trace_frame().copy()


# Backward-compatible name used by the first rebuild package.
InstrumentedTestWiseDeletionPC = InstrumentedTestWiseDeletionPC
