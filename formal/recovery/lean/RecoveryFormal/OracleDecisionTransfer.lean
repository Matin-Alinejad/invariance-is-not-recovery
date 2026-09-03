import Mathlib

open MeasureTheory

namespace RecoveryFormal

/-- Equality of the complete finite decision vector transfers through any deterministic algorithm. -/
theorem deterministic_output_eq
    {ι O : Type*} (A : (ι → Bool) → O) (d d' : ι → Bool)
    (h : d = d') : A d = A d' := by
  rw [h]

/-- Contrapositive form: an output mismatch requires a decision-coordinate mismatch. -/
theorem output_mismatch_has_coordinate
    {ι O : Type*} [Fintype ι]
    (A : (ι → Bool) → O) (d d' : ι → Bool)
    (h : A d ≠ A d') : ∃ i, d i ≠ d' i := by
  by_contra hcon
  push_neg at hcon
  exact h (deterministic_output_eq A d d' (funext hcon))

/-- Pointwise event inclusion for random decision vectors. -/
theorem output_error_subset_coordinate_errors
    {Ω ι O : Type*} [Fintype ι]
    (A : (ι → Bool) → O)
    (d d' : Ω → ι → Bool) :
    {ω | A (d ω) ≠ A (d' ω)} ⊆ ⋃ i, {ω | d ω i ≠ d' ω i} := by
  intro ω hω
  obtain ⟨i, hi⟩ := output_mismatch_has_coordinate A (d ω) (d' ω) hω
  exact Set.mem_iUnion.mpr ⟨i, hi⟩

/-- Measure-theoretic finite-union probability bound: the probability that the deterministic
search map produces mismatched outputs is at most the sum, over decision coordinates, of the
probabilities that the individual CI-decisions disagree. No independence of the CI-test errors
is assumed; this is pure countable/finite subadditivity of the measure. -/
theorem output_error_prob_le_sum
    {Ω ι O : Type*} [Fintype ι]
    {mΩ : MeasurableSpace Ω} (μ : Measure Ω)
    (A : (ι → Bool) → O)
    (d d' : Ω → ι → Bool) :
    μ {ω | A (d ω) ≠ A (d' ω)} ≤ ∑ i, μ {ω | d ω i ≠ d' ω i} := by
  calc
    μ {ω | A (d ω) ≠ A (d' ω)}
        ≤ μ (⋃ i, {ω | d ω i ≠ d' ω i}) :=
          measure_mono (output_error_subset_coordinate_errors A d d')
    _ ≤ ∑ i, μ {ω | d ω i ≠ d' ω i} :=
          measure_iUnion_fintype_le μ (fun i => {ω | d ω i ≠ d' ω i})

#print axioms deterministic_output_eq
#print axioms output_mismatch_has_coordinate
#print axioms output_error_subset_coordinate_errors
#print axioms output_error_prob_le_sum

end RecoveryFormal
