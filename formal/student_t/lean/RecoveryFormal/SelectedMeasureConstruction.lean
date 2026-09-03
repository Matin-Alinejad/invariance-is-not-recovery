import Mathlib
import RecoveryFormal.BoundedGaussianSelfMasking
import RecoveryFormal.FiniteCIDefinitionBridge

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace RecoveryFormal
namespace ConditionalThinning

variable {α : Type*} [MeasurableSpace α]

/-- Real retention weight embedded into `ℝ≥0∞`.  The downstream theorem assumes
measurability and `0 ≤ w ≤ 1`; this definition itself is deliberately total. -/
noncomputable def weightENN (w : α → ℝ) : α → ℝ≥0∞ :=
  fun x => ENNReal.ofReal (w x)

/-- Unnormalized retained-row measure `w · μ`. -/
noncomputable def retainedNumerator (μ : Measure α) (w : α → ℝ) : Measure α :=
  μ.withDensity (weightENN w)

/-- Unnormalized discarded-row measure `(1-w) · μ`. -/
noncomputable def discardedNumerator (μ : Measure α) (w : α → ℝ) : Measure α :=
  μ.withDensity (fun x => ENNReal.ofReal (1 - w x))

/-- Query-retention mass.  Under the target assumptions this equals `∫ w dμ`. -/
noncomputable def retentionMass (μ : Measure α) (w : α → ℝ) : ℝ≥0∞ :=
  retainedNumerator μ w Set.univ

/-- Normalized selected law.  The downstream development proves it is a
probability measure when `0 < retentionMass μ w`. -/
noncomputable def selectedLaw (μ : Measure α) (w : α → ℝ) : Measure α :=
  (retentionMass μ w)⁻¹ • retainedNumerator μ w

/-- Canonical one-row law of `(value, retained?)`.  This avoids making the
independent-uniform representation the primary object: the `true` fibre is
`w·μ` and the `false` fibre is `(1-w)·μ`. -/
noncomputable def markedRowLaw (μ : Measure α) (w : α → ℝ) : Measure (α × Bool) :=
  Measure.map (fun x => (x, true)) (retainedNumerator μ w) +
  Measure.map (fun x => (x, false)) (discardedNumerator μ w)

/-- The fixed finite sample space used throughout retained-row thinning. -/
abbrev MarkedSample (α : Type*) (n : ℕ) := Fin n → α × Bool

/-- Value component of a marked row. -/
def rowValue {n : ℕ} (z : MarkedSample α n) (i : Fin n) : α := (z i).1

/-- Retention bit of a marked row. -/
def rowRetained {n : ℕ} (z : MarkedSample α n) (i : Fin n) : Bool := (z i).2

/-- Retained index set. -/
def retainedSet {n : ℕ} (z : MarkedSample α n) : Finset (Fin n) :=
  Finset.univ.filter (fun i => rowRetained z i = true)

/-- Retained count. -/
def retainedCount {n : ℕ} (z : MarkedSample α n) : ℕ :=
  (retainedSet z).card

/-- Values indexed by a deterministic retained set.  The fixed-pattern law
is most naturally stated on this subtype before reindexing by `Fin I.card`. -/
def valuesOn {n : ℕ} (I : Finset (Fin n)) (z : MarkedSample α n) : I → α :=
  fun i => rowValue z i.1

end ConditionalThinning
end RecoveryFormal
