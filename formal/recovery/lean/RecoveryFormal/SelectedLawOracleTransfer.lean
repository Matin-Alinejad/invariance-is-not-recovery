import RecoveryFormal.FiniteSeparableSelectionCI
import RecoveryFormal.GaussianPreservingSelection

namespace RecoveryFormal

/-- selected-law transfer: for every prespecified query, strictly positive coordinate-separable
selection preserves and reflects its oracle CI decision. -/
theorem oracle_decision_preserved
    {ι X Y Z : Type*}
    (p : ι → X → Y → Z → ℝ)
    (a : ι → X → ℝ) (b : ι → Y → ℝ) (c : ι → Z → ℝ)
    (ha : ∀ q x, 0 < a q x) (hb : ∀ q y, 0 < b q y)
    (hc : ∀ q z, 0 < c q z) :
    ∀ q, FourPointCI (selectedMass (p q) (a q) (b q) (c q)) ↔ FourPointCI (p q) := by
  intro q
  exact separable_selection_ci_iff (p q) (a q) (b q) (c q)
    (ha q) (hb q) (hc q)

#print axioms oracle_decision_preserved
end RecoveryFormal
