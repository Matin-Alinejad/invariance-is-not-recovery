import Mathlib
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
namespace RecoveryFormal
namespace GaussianPartialCorrelation

noncomputable def partialCorrelationDf (m s : ℕ) : ℕ := m - s - 2
noncomputable def chiSquareMeasure (df : ℕ) : Measure ℝ :=
  Measure.map (fun x : ℝ => 2 * x) (gammaMeasure ((df : ℝ) / 2) (1 / 2))
noncomputable def studentTMeasure (df : ℕ) : Measure ℝ :=
  Measure.map (fun z : ℝ × ℝ => z.1 / Real.sqrt (z.2 / (df : ℝ)))
    ((gaussianReal 0 1).prod (chiSquareMeasure df))

/-- A positive-degree chi-square measure has total mass one. -/
theorem chiSquareMeasure_univ (df : ℕ) (hdf : 0 < df) :
    chiSquareMeasure df Set.univ = 1 := by
  have ha : (0 : ℝ) < (df : ℝ) / 2 := by positivity
  letI := isProbabilityMeasure_gammaMeasure ha (by norm_num : (0 : ℝ) < 1 / 2)
  unfold chiSquareMeasure
  rw [Measure.map_apply]
  · exact measure_univ
  · fun_prop
  · exact MeasurableSet.univ

/-- A chi-square variable is strictly positive almost surely (in particular it
has no mass on the nonpositive half-line). -/
theorem chiSquareMeasure_Iic_zero (df : ℕ) :
    chiSquareMeasure df (Set.Iic 0) = 0 := by
  unfold chiSquareMeasure
  rw [Measure.map_apply]
  · have hpre : (fun x : ℝ => 2 * x) ⁻¹' Set.Iic 0 = Set.Iic 0 := by
      ext x
      simp
    rw [hpre]
    rw [show Set.Iic (0 : ℝ) = Set.Iio 0 ∪ {0} by
      ext x
      simp [le_iff_lt_or_eq]]
    apply measure_union_null
    · rw [gammaMeasure, withDensity_apply _ measurableSet_Iio]
      exact lintegral_gammaPDF_of_nonpos le_rfl
    · exact withDensity_absolutelyContinuous volume _ Real.volume_singleton
  · fun_prop
  · exact measurableSet_Iic

/-- The Student-t pushforward is a probability measure for positive degrees of freedom. -/
theorem studentTMeasure_univ (df : ℕ) (hdf : 0 < df) :
    studentTMeasure df Set.univ = 1 := by
  have hchi := chiSquareMeasure_univ df hdf
  letI : IsFiniteMeasure (chiSquareMeasure df) :=
    IsFiniteMeasure.mk (by rw [hchi]; norm_num)
  unfold studentTMeasure
  rw [Measure.map_apply]
  · simp only [Set.preimage_univ]
    rw [Measure.prod_apply MeasurableSet.univ]
    simp [hchi]
  · fun_prop
  · exact MeasurableSet.univ

end GaussianPartialCorrelation
end RecoveryFormal
