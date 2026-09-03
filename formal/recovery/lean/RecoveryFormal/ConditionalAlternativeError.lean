import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace RecoveryFormal

/-- alternative-error input decision-level alternative-error conclusion.  A calibrated failure-to-
reject event is exactly the Boolean decision-error event under the alternative. -/
theorem conditional_alternative_error
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (decision : Ω → Bool) (conditioningEvent failureEvent : Set Ω)
    (epsilon : ℝ≥0∞)
    (hdecision : ∀ ω, decision ω = false ↔ ω ∈ failureEvent)
    (hcalibrated : (μ[failureEvent | conditioningEvent]) ≤ epsilon) :
    (μ[{ω | decision ω ≠ true} | conditioningEvent]) ≤ epsilon := by
  have heq : {ω | decision ω ≠ true} = failureEvent := by
    ext ω
    cases h : decision ω <;> simp [h, hdecision]
  rwa [heq]

#print axioms conditional_alternative_error
end RecoveryFormal
