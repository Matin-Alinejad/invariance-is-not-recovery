import Mathlib

namespace RecoveryCore

/-- F1 written directly in terms of nonnegative confusion counts. -/
noncomputable def f1Counts (tp fp fn : ℝ) : ℝ :=
  if 2 * tp + fp + fn = 0 then 0 else (2 * tp) / (2 * tp + fp + fn)

/-- With a positive denominator, the guarded definition reduces to the usual formula. -/
theorem f1Counts_eq (tp fp fn : ℝ)
    (hden : 2 * tp + fp + fn ≠ 0) :
    f1Counts tp fp fn = (2 * tp) / (2 * tp + fp + fn) := by
  unfold f1Counts
  rw [if_neg hden]

/-- If a true edge set has size `s`, then `tp = s - fn`. -/
theorem true_positive_identity (s tp fn : ℝ)
    (h : tp + fn = s) : tp = s - fn := by
  linarith

/-- The denominator is positive under the natural count assumptions and `s>0`. -/
theorem f1_den_pos (s fp fn : ℝ)
    (hs : 0 < s) (hfp : 0 ≤ fp) (hfn0 : 0 ≤ fn) (hfns : fn ≤ s) :
    0 < 2 * (s - fn) + fp + fn := by
  linarith

end RecoveryCore
