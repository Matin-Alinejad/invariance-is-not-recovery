import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace RecoveryFormal

/-- partial-correlation null decision-level Type-I conclusion.  A calibrated null rejection event is
exactly the Boolean decision-error event. -/
theorem conditional_typeI
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (decision : Ω → Bool) (conditioningEvent rejectionEvent : Set Ω)
    (epsilon : ℝ≥0∞)
    (hdecision : ∀ ω, decision ω = true ↔ ω ∈ rejectionEvent)
    (hcalibrated : (μ[rejectionEvent | conditioningEvent]) ≤ epsilon) :
    (μ[{ω | decision ω ≠ false} | conditioningEvent]) ≤ epsilon := by
  have heq : {ω | decision ω ≠ false} = rejectionEvent := by
    ext ω
    cases h : decision ω <;> simp [h, hdecision]
  rwa [heq]

#print axioms conditional_typeI
end RecoveryFormal
