"""Exact finite-state audit of the separable self-masking CI identity.

The audit uses :class:`fractions.Fraction`, so the reported equalities are exact
rational identities rather than floating-point approximations.  It is a
computational verification of the stated theorem, not a substitute for the
measure-theoretic proof.
"""
from __future__ import annotations

import argparse
import json
import random
from fractions import Fraction
from pathlib import Path
from typing import Dict, Iterable, Tuple

REPO_ROOT = Path(__file__).resolve().parents[2]

State = Tuple[int, int, int]  # (x, y, z), all binary


def _normalize(weights: Dict[State, Fraction]) -> Dict[State, Fraction]:
    total = sum(weights.values(), Fraction(0, 1))
    if total <= 0:
        raise ValueError("Distribution has non-positive total mass")
    return {state: mass / total for state, mass in weights.items()}


def _conditional_independence_determinants(distribution: Dict[State, Fraction]) -> Dict[int, Fraction]:
    """Return the 2x2 determinant for X and Y within every Z stratum.

    For a strictly positive binary distribution, X ⟂ Y | Z=z exactly when
    p00(z) p11(z) - p01(z) p10(z) = 0.  Normalizing within a stratum is
    unnecessary because the common denominator cancels.
    """
    out: Dict[int, Fraction] = {}
    for z in (0, 1):
        p00 = distribution[(0, 0, z)]
        p01 = distribution[(0, 1, z)]
        p10 = distribution[(1, 0, z)]
        p11 = distribution[(1, 1, z)]
        out[z] = p00 * p11 - p01 * p10
    return out


def _random_positive_fraction(rng: random.Random, max_numerator: int = 17) -> Fraction:
    return Fraction(rng.randint(1, max_numerator), rng.randint(max_numerator, 2 * max_numerator))


def _random_ci_distribution(rng: random.Random) -> Dict[State, Fraction]:
    """Generate a strictly positive law satisfying X ⟂ Y | Z by construction."""
    pz1 = _random_positive_fraction(rng)
    if pz1 >= 1:
        pz1 = Fraction(1, 2)
    pz = {0: 1 - pz1, 1: pz1}
    px1 = {z: _random_positive_fraction(rng) for z in (0, 1)}
    py1 = {z: _random_positive_fraction(rng) for z in (0, 1)}
    for table in (px1, py1):
        for z in table:
            if table[z] >= 1:
                table[z] = Fraction(1, 2)
    weights: Dict[State, Fraction] = {}
    for x in (0, 1):
        for y in (0, 1):
            for z in (0, 1):
                px = px1[z] if x else 1 - px1[z]
                py = py1[z] if y else 1 - py1[z]
                weights[(x, y, z)] = pz[z] * px * py
    return _normalize(weights)


def _apply_selection(
    distribution: Dict[State, Fraction],
    selection: Dict[State, Fraction],
) -> Dict[State, Fraction]:
    if any(prob <= 0 or prob > 1 for prob in selection.values()):
        raise ValueError("Selection probabilities must be in (0,1]")
    return _normalize({state: distribution[state] * selection[state] for state in distribution})


def _separable_selection(rng: random.Random) -> Dict[State, Fraction]:
    qx = {x: _random_positive_fraction(rng) for x in (0, 1)}
    qy = {y: _random_positive_fraction(rng) for y in (0, 1)}
    qz = {z: _random_positive_fraction(rng) for z in (0, 1)}
    return {(x, y, z): qx[x] * qy[y] * qz[z] for x in (0, 1) for y in (0, 1) for z in (0, 1)}


def _fraction_json(value: Fraction) -> str:
    return f"{value.numerator}/{value.denominator}"


def audit(cases: int = 250, seed: int = 20260724) -> dict:
    """Verify the finite-state selection identity used by the theorem/experiment interface."""
    if cases <= 0:
        raise ValueError("cases must be positive")
    rng = random.Random(seed)
    preservation_failures = []
    reverse_failures = []
    for case_index in range(cases):
        complete = _random_ci_distribution(rng)
        selection = _separable_selection(rng)
        observed = _apply_selection(complete, selection)
        complete_det = _conditional_independence_determinants(complete)
        observed_det = _conditional_independence_determinants(observed)
        if any(value != 0 for value in complete_det.values()) or any(value != 0 for value in observed_det.values()):
            preservation_failures.append({
                "case": case_index,
                "complete_determinants": {str(z): _fraction_json(v) for z, v in complete_det.items()},
                "observed_determinants": {str(z): _fraction_json(v) for z, v in observed_det.items()},
            })
        # Positivity makes the transformation invertible: divide by q and renormalize.
        reconstructed = _normalize({state: observed[state] / selection[state] for state in observed})
        if reconstructed != complete:
            reverse_failures.append({"case": case_index})

    # Exact non-separable counterexample: X,Y independent fair bits (Z is
    # irrelevant), but selection favours agreement and creates association.
    complete_uniform = {(x, y, z): Fraction(1, 8) for x in (0, 1) for y in (0, 1) for z in (0, 1)}
    nonseparable = {
        (x, y, z): (Fraction(4, 5) if x == y else Fraction(1, 5))
        for x in (0, 1) for y in (0, 1) for z in (0, 1)
    }
    selected_nonseparable = _apply_selection(complete_uniform, nonseparable)
    before_det = _conditional_independence_determinants(complete_uniform)
    after_det = _conditional_independence_determinants(selected_nonseparable)

    return {
        "cases": cases,
        "seed": seed,
        "arithmetic": "exact rational (fractions.Fraction)",
        "separable_selection_preservation_failures": len(preservation_failures),
        "positive_selection_inverse_failures": len(reverse_failures),
        "first_preservation_failures": preservation_failures[:5],
        "first_inverse_failures": reverse_failures[:5],
        "nonseparable_counterexample": {
            "complete_determinants": {str(z): _fraction_json(v) for z, v in before_det.items()},
            "selected_determinants": {str(z): _fraction_json(v) for z, v in after_det.items()},
            "breaks_conditional_independence": any(value != 0 for value in after_det.values()),
        },
        "interpretation": (
            "Positive coordinate-wise separable selection preserves and reflects conditional "
            "independence in these exact finite-state cases. A positive but non-separable "
            "selection rule can create dependence. This validates the algebraic identity "
            "used by the theorem but does not replace its general proof."
        ),
    }


def main() -> None:
    """Run the finite-state selection-identity audit and write its report."""
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--cases", type=int, default=250)
    parser.add_argument("--seed", type=int, default=20260724)
    parser.add_argument("--output", default=str(REPO_ROOT / "selection_identity_verification.json"))
    args = parser.parse_args()
    result = audit(args.cases, args.seed)
    output = Path(args.output)
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
