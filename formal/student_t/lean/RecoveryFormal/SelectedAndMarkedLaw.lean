import RecoveryFormal.TargetArchitecture

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace RecoveryFormal
namespace ConditionalThinning

variable {α : Type*} [MeasurableSpace α]

/-- The two unnormalised fibres add back to the source probability law. -/
theorem retained_add_discarded
    (μ : Measure α) (w : α → ℝ) (hwmeas : Measurable w)
    (hw0 : ∀ x, 0 ≤ w x) (hw1 : ∀ x, w x ≤ 1) :
    retainedNumerator μ w + discardedNumerator μ w = μ := by
  unfold retainedNumerator discardedNumerator weightENN
  rw [← withDensity_add_left hwmeas.ennreal_ofReal]
  have heq : (fun x => ENNReal.ofReal (w x)) +
      (fun x => ENNReal.ofReal (1 - w x)) = 1 := by
    funext x
    simp only [Pi.add_apply, Pi.one_apply]
    rw [← ENNReal.ofReal_add (hw0 x) (sub_nonneg.mpr (hw1 x))]
    simp
  rw [heq, withDensity_one]

/-- The discarded mass is the complement of the retained mass. -/
theorem discardedNumerator_univ
    (μ : Measure α) [IsProbabilityMeasure μ] (w : α → ℝ)
    (hwmeas : Measurable w) (hw0 : ∀ x, 0 ≤ w x) (hw1 : ∀ x, w x ≤ 1) :
    discardedNumerator μ w Set.univ = 1 - retentionMass μ w := by
  have h := congrArg (fun m : Measure α => m Set.univ)
    (retained_add_discarded μ w hwmeas hw0 hw1)
  simp only [Measure.add_apply, measure_univ, retentionMass] at h
  have htop : retainedNumerator μ w Set.univ ≠ ∞ := by
    intro hbad
    rw [hbad] at h
    simp at h
  unfold retentionMass
  symm
  apply ENNReal.sub_eq_of_eq_add htop
  simpa [add_comm] using h.symm

/-- The normalized selected measure has mass one; normalization is derived. -/
theorem selectedLaw_isProbability
    (μ : Measure α) [IsProbabilityMeasure μ] (w : α → ℝ)
    (hq0 : retentionMass μ w ≠ 0) (hqtop : retentionMass μ w ≠ ∞) :
    IsProbabilityMeasure (selectedLaw μ w) := by
  rw [isProbabilityMeasure_iff]
  simp only [selectedLaw, Measure.smul_apply, smul_eq_mul]
  exact ENNReal.inv_mul_cancel hq0 hqtop

/-- The selected numerator is its mass times the selected probability law. -/
theorem retainedNumerator_eq_mass_smul_selectedLaw
    (μ : Measure α) (w : α → ℝ)
    (hq0 : retentionMass μ w ≠ 0) (hqtop : retentionMass μ w ≠ ∞) :
    retainedNumerator μ w = retentionMass μ w • selectedLaw μ w := by
  unfold selectedLaw
  rw [smul_smul, ENNReal.mul_inv_cancel hq0 hqtop, one_smul]

/-- The canonical marked-row construction is itself a probability measure. -/
theorem markedRowLaw_isProbability
    (μ : Measure α) [IsProbabilityMeasure μ] (w : α → ℝ)
    (hwmeas : Measurable w) (hw0 : ∀ x, 0 ≤ w x) (hw1 : ∀ x, w x ≤ 1) :
    IsProbabilityMeasure (markedRowLaw μ w) := by
  rw [isProbabilityMeasure_iff]
  unfold markedRowLaw
  rw [Measure.add_apply]
  rw [Measure.map_apply (by fun_prop) MeasurableSet.univ]
  rw [Measure.map_apply (by fun_prop) MeasurableSet.univ]
  have h := congrArg (fun m : Measure α => m Set.univ)
    (retained_add_discarded μ w hwmeas hw0 hw1)
  simpa [Measure.add_apply] using h

/-- Exact retained fibre of the canonical one-row law. -/
theorem markedRowLaw_true_cylinder
    (μ : Measure α) (w : α → ℝ) (A : Set α) (hA : MeasurableSet A) :
    markedRowLaw μ w (A ×ˢ ({true} : Set Bool)) = retainedNumerator μ w A := by
  rw [markedRowLaw, Measure.add_apply]
  rw [Measure.map_apply (by fun_prop)
    (hA.prod (measurableSet_singleton _))]
  rw [Measure.map_apply (by fun_prop)
    (hA.prod (measurableSet_singleton _))]
  simp

/-- Exact discarded fibre of the canonical one-row law. -/
theorem markedRowLaw_false_cylinder
    (μ : Measure α) (w : α → ℝ) (A : Set α) (hA : MeasurableSet A) :
    markedRowLaw μ w (A ×ˢ ({false} : Set Bool)) = discardedNumerator μ w A := by
  rw [markedRowLaw, Measure.add_apply]
  rw [Measure.map_apply (by fun_prop)
    (hA.prod (measurableSet_singleton _))]
  rw [Measure.map_apply (by fun_prop)
    (hA.prod (measurableSet_singleton _))]
  simp

end ConditionalThinning
end RecoveryFormal
