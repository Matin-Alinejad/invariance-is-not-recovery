#!/usr/bin/env python3
"""Verify regenerated reference figures and computational/result tables."""
from __future__ import annotations
import argparse
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
FIGURES = [
    'primary_scaling',
    'precision_recall_shift',
    'retention_sensitivity',
    'threshold_sensitivity',
    'matched_local_comparison',
    'information_rate',
]
TABLES = [
    'experiment_program',
    'information_rate',
    'matched_local',
    'population_margin_diagnostics',
    'retention_sensitivity',
    'sample_growth',
    'search_depth_scope',
    'threshold_sensitivity',
]


def render_ppm(pdf: Path, prefix: Path) -> bytes:
    """Render one PDF page to a PPM image for deterministic pixel comparison."""
    exe = shutil.which('pdftoppm')
    if not exe:
        raise SystemExit('pdftoppm is required for exact rendered-figure verification. Install poppler-utils.')
    subprocess.run([exe, '-f', '1', '-singlefile', '-r', '120', str(pdf), str(prefix)], check=True,
                   stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    return prefix.with_suffix('.ppm').read_bytes()


def main() -> int:
    """Regenerate and compare all released reference figures and LaTeX tables."""
    ap = argparse.ArgumentParser(description='Regenerate and verify the released reference figures and computational/result tables.')
    ap.add_argument('--evidence-dir', default=str(ROOT/'evidence'))
    ap.add_argument('--output-dir', default=str(ROOT/'results'/'regenerated_artifacts'))
    ap.add_argument('--reference-dir', default=str(ROOT/'reference'))
    a = ap.parse_args()
    evidence = Path(a.evidence_dir).resolve()
    out = Path(a.output_dir).resolve()
    ref = Path(a.reference_dir).resolve()
    if out.exists():
        shutil.rmtree(out)
    subprocess.run([
        sys.executable, str(ROOT/'analysis'/'generate_reference_artifacts.py'),
        '--evidence-dir', str(evidence), '--output-dir', str(out)
    ], check=True)

    problems: list[str] = []
    for name in TABLES:
        expected = ref/'tables'/f'{name}.tex'
        got = out/'tables'/f'{name}.tex'
        if not expected.exists() or not got.exists():
            problems.append(f'missing table: {name}')
        elif expected.read_bytes() != got.read_bytes():
            problems.append(f'table differs byte-for-byte: {name}')

    with tempfile.TemporaryDirectory(prefix='artifact_render_') as td:
        td = Path(td)
        for name in FIGURES:
            expected = ref/'figures'/f'{name}.pdf'
            got = out/'figures'/f'{name}.pdf'
            if not expected.exists() or not got.exists():
                problems.append(f'missing figure: {name}')
                continue
            if render_ppm(expected, td/f'{name}_ref') != render_ppm(got, td/f'{name}_got'):
                problems.append(f'rendered pixels differ at 120 dpi: {name}')

    tikz = ref/'figures'/'recovery_pipeline.tex'
    if not tikz.exists() or tikz.stat().st_size == 0:
        problems.append('native TeX recovery-pipeline schematic missing')

    if problems:
        print('ARTIFACT VERIFICATION: FAIL')
        for p in problems:
            print(' -', p)
        return 2
    print(f'ARTIFACT VERIFICATION: PASS ({len(FIGURES)}/6 figures pixel-identical; {len(TABLES)}/8 computational/result tables byte-identical; native TeX schematic present)')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
