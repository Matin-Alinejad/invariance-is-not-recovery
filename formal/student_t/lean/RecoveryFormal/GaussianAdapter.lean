import RecoveryFormal.CountMixture

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal BigOperators

namespace RecoveryFormal
namespace ConditionalThinning

variable {α : Type*} [MeasurableSpace α]

/-- Gaussian/specified-selected-law adapter.  This theorem contains no new
probability argument: it rewrites the product law supplied by
`conditional_count_ordered_productLaw`. -/
theorem conditional_count_gaussianLaw {n m : ℕ} (hm : m ≤ n)
    (μ : Measure α) [IsProbabilityMeasure μ] (w : α → ℝ)
    (hwmeas : Measurable w) (hw0 : ∀ x, 0 ≤ w x) (hw1 : ∀ x, w x ≤ 1)
    (hq0 : retentionMass μ w ≠ 0) (hqtop : retentionMass μ w ≠ ∞)
    (hq1 : retentionMass μ w ≠ 1)
    (G : Measure α) (hG : selectedLaw μ w = G) :
    ∃ retainedVector : MarkedSample α n → Fin m → α,
      Measurable retainedVector ∧
      Measure.map retainedVector ((markedSampleLaw μ w n)[|countEvent m]) =
        Measure.pi (fun _ : Fin m => G) := by
  obtain ⟨retainedVector, hmeas, hlaw⟩ :=
    conditional_count_ordered_productLaw hm μ w hwmeas hw0 hw1 hq0 hqtop hq1
  refine ⟨retainedVector, hmeas, ?_⟩
  simpa [hG] using hlaw

end ConditionalThinning
end RecoveryFormal
