import RecoveryCore.Basic

namespace RecoveryCore

/-- A deterministic total-error bound gives a lower bound on F1.

This is the direction supported by an upper bound on FP/FN. -/
theorem f1_lower_of_total_error
    (s fp fn u : ℝ)
    (hs : 0 < s)
    (hfp : 0 ≤ fp)
    (hfn : 0 ≤ fn)
    (hfn_le : fn ≤ s)
    (hu : fp + fn ≤ u)
    (hu_lt : u < s) :
    f1Counts (s - fn) fp fn ≥ 2 * (s - u) / (2 * s + u) := by
  have hden1 : 0 < 2 * (s - fn) + fp + fn := f1_den_pos s fp fn hs hfp hfn hfn_le
  have hden2 : 0 < 2 * s + u := by linarith
  rw [f1Counts_eq _ _ _ (ne_of_gt hden1), ge_iff_le, div_le_div_iff₀ hden2 hden1]
  nlinarith [hfp, hfn, hu, hu_lt, hs]

/-- The lower bound lies in `[0,1]` under its natural assumptions. -/
theorem f1_lower_bound_mem_unit
    (s u : ℝ) (hs : 0 < s) (hu0 : 0 ≤ u) (hu : u < s) :
    0 ≤ 2 * (s - u) / (2 * s + u) ∧
      2 * (s - u) / (2 * s + u) ≤ 1 := by
  have hden : 0 < 2 * s + u := by linarith
  refine ⟨div_nonneg (by linarith) (by linarith), ?_⟩
  rw [div_le_one hden]
  linarith

end RecoveryCore
