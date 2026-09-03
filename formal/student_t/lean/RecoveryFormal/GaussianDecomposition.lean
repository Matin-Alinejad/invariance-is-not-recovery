import RecoveryFormal.ResidualGeometry
open MeasureTheory ProbabilityTheory
namespace RecoveryFormal
namespace GaussianPartialCorrelation

/-- Exact structural contract needed by the transformation theorem.  It records
measurability, the two marginal laws, independence, and the residual correlation
identity.  It is an intermediate hypothesis, not a definition of an iid Gaussian
row model. -/
structure HasGaussianResidualRepresentation {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (m s : ℕ) (rhat : Ω → ℝ) where
  Z : Ω → ℝ
  V : Ω → ℝ
  measurable_Z : Measurable Z
  measurable_V : Measurable V
  measurable_rhat : Measurable rhat
  map_Z : Measure.map Z P = gaussianReal 0 1
  map_V : Measure.map V P = chiSquareMeasure (partialCorrelationDf m s)
  indep : IndepFun Z V P
  corr_ae : ∀ᵐ ω ∂P, rhat ω = Z ω / Real.sqrt (Z ω ^ 2 + V ω)

/-!
## Paper-facing Gaussian layer

Deriving this structure from iid rows with a specified nonsingular multivariate
Gaussian pushforward law remains a separate formalization task.  In particular,
this file does not rename the desired residual conclusion as a “Gaussian model”:
the missing derivation must prove centered-design full rank, orthogonal residual
laws, chi-square support, independence, and the correlation identity from the row
law.
-/

end GaussianPartialCorrelation
end RecoveryFormal
