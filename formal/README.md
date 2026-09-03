# Formal corroboration

This directory contains Lean 4 / Mathlib source that independently checks the finite-combinatorial, probabilistic, Gaussian-null, recovery-composition, and information-theoretic kernels used in the accompanying mathematical development.

The source is organized by role rather than by stated theorem number:

- `recovery/`: separable selection, Gaussian-preserving selection, retained-count bounds, query budgets, exact-recovery/F1 transfer, retained-row factorization, and end-to-end recovery composition.
- `student_t/`: residual geometry, the normal/chi-square representation, the exact Student-t transform for partial correlation, and the selected-row adapter.
- `information/`: the sparse Gaussian pair construction, observed-data information calculation, and arbitrary-estimator lower bound.

Each subdirectory is a standalone Lean project pinned to Lean 4.28.0 and Mathlib 4.28.0. To compile all three:

```bash
bash formal/build_all.sh
```

Or build one component directly:

```bash
cd formal/recovery && lake build
cd ../student_t && lake build
cd ../information && lake build
```

The formal source corroborates the encoded mathematical components under the hypotheses stated in each module; it does not enlarge their scope.
