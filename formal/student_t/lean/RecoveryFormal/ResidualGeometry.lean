import RecoveryFormal.StudentTMeasure
open Matrix MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace RecoveryFormal
namespace GaussianPartialCorrelation

/-- Data for `m` observations of two queried variables and `s` conditioning variables. -/
structure PartialCorrSample (m s : ℕ) where
  x : Fin m → ℝ
  y : Fin m → ℝ
  z : Fin m → Fin s → ℝ

/-- The numerical form of a correlation of two residual vectors.  This definition
records the residual vectors; constructing them from a Gaussian row
model is deliberately a separate layer. -/
def HasSamplePartialCorrelation {m s : ℕ} (_D : PartialCorrSample m s) (r : ℝ) : Prop :=
  ∃ ux uy : Fin m → ℝ,
    r = (∑ k, ux k * uy k) /
      Real.sqrt ((∑ k, (ux k) ^ 2) * (∑ k, (uy k) ^ 2))

/-!
The residual-correlation layer deliberately stops at the numerical sample statistic.
A probabilistic theorem that instantiates this definition must separately specify the
row-vector law and establish the required almost-sure rank condition from that law.
-/

end GaussianPartialCorrelation
end RecoveryFormal
