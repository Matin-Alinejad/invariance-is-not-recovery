#!/usr/bin/env python3
"""Run the registered causal-skeleton recovery experiments."""
from pathlib import Path
import runpy

ROOT = Path(__file__).resolve().parent
runpy.run_path(
    str(ROOT / "code" / "experiments" / "run_recovery_experiments.py"),
    run_name="__main__",
)
