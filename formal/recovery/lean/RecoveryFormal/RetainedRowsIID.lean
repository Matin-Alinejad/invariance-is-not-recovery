import Mathlib

open MeasureTheory ProbabilityTheory
namespace RecoveryFormal

/-- retained-row thinning: measurable rowwise events factor under an independent row family.  The
measurability is stated in each row's pullback sigma-algebra, exactly expressing
that the event depends only on that retained row. -/
theorem retained_rows_iid
    {Ω R : Type*} [MeasurableSpace Ω] [MeasurableSpace R]
    {n : ℕ} (μ : Measure Ω) (row : Fin n → Ω → R)
    (hindep : iIndepFun row μ) (event : Fin n → Set Ω)
    (hevent : ∀ r, @MeasurableSet Ω (MeasurableSpace.comap (row r) inferInstance)
      (event r)) :
    μ (⋂ r, event r) = ∏ r, μ (event r) :=
  hindep.meas_iInter hevent

#print axioms retained_rows_iid
end RecoveryFormal
