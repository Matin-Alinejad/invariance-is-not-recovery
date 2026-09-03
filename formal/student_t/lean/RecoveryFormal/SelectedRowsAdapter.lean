import RecoveryFormal.ExactNullLaw
import RecoveryFormal.GaussianAdapter

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal BigOperators

namespace RecoveryFormal
namespace GaussianPartialCorrelation

open ConditionalThinning

/-- Selected-row interface to partial-correlation null.  retained-row thinning supplies the conditional product law of
an actual retained vector.  The equality `hG` separately identifies the selected
one-row law with `G`; the residual representation on the resulting product
measure remains an explicit hypothesis until the Gaussian-row derivation is
formalized. -/
theorem selected_rows_studentT_adapter
    {α : Type*} [MeasurableSpace α] {n m s : ℕ} (hm : m ≤ n)
    (μ : Measure α) [IsProbabilityMeasure μ] (w : α → ℝ)
    (hwmeas : Measurable w) (hw0 : ∀ x, 0 ≤ w x) (hw1 : ∀ x, w x ≤ 1)
    (hq0 : retentionMass μ w ≠ 0)
    (hqtop : retentionMass μ w ≠ ∞)
    (hq1 : retentionMass μ w ≠ 1)
    (G : Measure α) (hG : selectedLaw μ w = G)
    (rhat : (Fin m → α) → ℝ)
    (hrep : HasGaussianResidualRepresentation
      (Measure.pi (fun _ : Fin m => G)) m s rhat)
    (hsize : s + 2 < m) :
    ∃ retainedVector : MarkedSample α n → Fin m → α,
      Measurable retainedVector ∧
      Measure.map
          (fun sample => partialCorrT m s (rhat (retainedVector sample)))
          ((markedSampleLaw μ w n)[|countEvent m]) =
        studentTMeasure (partialCorrelationDf m s) := by
  obtain ⟨retainedVector, hmeas, hlaw⟩ := conditional_count_gaussianLaw hm μ w hwmeas hw0 hw1 hq0 hqtop hq1 G hG
  haveI : IsProbabilityMeasure G := by
    rw [← hG]
    exact selectedLaw_isProbability μ w hq0 hqtop
  refine ⟨retainedVector, hmeas, ?_⟩
  have hmeas_rhat := hrep.measurable_rhat
  have hmeas_partialCorrT : Measurable (partialCorrT m s) := by
    unfold partialCorrT
    exact Measurable.mul measurable_id 
      (Real.continuous_sqrt.measurable.comp 
        (Measurable.div measurable_const (Measurable.sub measurable_const (measurable_id.pow_const 2))))
  have hmeas_comp : Measurable (partialCorrT m s ∘ rhat) := hmeas_partialCorrT.comp hmeas_rhat
  calc Measure.map (fun sample => partialCorrT m s (rhat (retainedVector sample))) 
        ((markedSampleLaw μ w n)[|countEvent m]) 
      = Measure.map ((partialCorrT m s ∘ rhat) ∘ retainedVector) 
        ((markedSampleLaw μ w n)[|countEvent m]) := by rfl
    _ = Measure.map (partialCorrT m s ∘ rhat) 
        (Measure.map retainedVector ((markedSampleLaw μ w n)[|countEvent m])) := by 
          rw [Measure.map_map hmeas_comp hmeas]
    _ = Measure.map (partialCorrT m s ∘ rhat) (Measure.pi fun x => G) := by rw [hlaw]
    _ = Measure.map (fun ω => partialCorrT m s (rhat ω)) (Measure.pi fun x => G) := by rfl
    _ = studentTMeasure (partialCorrelationDf m s) := 
          sample_partial_correlation_studentT_of_representation _ m s rhat hrep hsize

end GaussianPartialCorrelation
end RecoveryFormal
