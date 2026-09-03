import RecoveryCore.DeterministicF1
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.Independence.Basic

open MeasureTheory ProbabilityTheory

namespace RecoveryCore

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)

/-- The event on which total error is at most `U/δ`. -/
def goodErrorEvent (err : Ω → ℝ) (U δ : ℝ) : Set Ω :=
  {ω | err ω ≤ U / δ}

/-- Markov-style high-probability control for a nonnegative integrable error variable.

Correction to the originally stated lemma: an `Integrable err μ` hypothesis is
required.  Without it the statement is false, because the Bochner integral of a
nonnegative *non*-integrable function is `0` by convention (`integral_undef`),
which makes `∫ err ∂μ ≤ U` vacuously true while the tail probability
`μ {err > U/δ}` can be arbitrarily close to `1`.  With integrability the bound is
exactly Markov's inequality. -/
theorem prob_goodErrorEvent
    [IsProbabilityMeasure μ]
    (err : Ω → ℝ) (U δ : ℝ)
    (herr_meas : Measurable err)
    (herr_int : Integrable err μ)
    (herr_nonneg : ∀ ω, 0 ≤ err ω)
    (hU : ∫ ω, err ω ∂μ ≤ U)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (hU0 : 0 ≤ U) :
    μ (goodErrorEvent err U δ) ≥ ENNReal.ofReal (1 - δ) := by
  have hmeas_s : MeasurableSet (goodErrorEvent err U δ) :=
    measurableSet_le herr_meas measurable_const
  have hae_nonneg : 0 ≤ᵐ[μ] err := Filter.Eventually.of_forall herr_nonneg
  have hsub : (goodErrorEvent err U δ)ᶜ ⊆ {ω | U / δ ≤ err ω} := by
    intro ω hω
    simp only [goodErrorEvent, Set.mem_compl_iff, Set.mem_setOf_eq, not_le] at hω
    exact le_of_lt hω
  have hcompl_le : μ.real (goodErrorEvent err U δ)ᶜ ≤ δ := by
    rcases eq_or_lt_of_le hU0 with hU0' | hUpos
    · -- `U = 0`: the error is `0` almost everywhere, so the complement is null.
      have hint0 : ∫ ω, err ω ∂μ = 0 :=
        le_antisymm (hU0'.symm ▸ hU) (integral_nonneg herr_nonneg)
      have hae0 : err =ᵐ[μ] 0 := by
        rwa [integral_eq_zero_iff_of_nonneg herr_nonneg herr_int] at hint0
      have hnull : μ (goodErrorEvent err U δ)ᶜ = 0 := by
        refine measure_mono_null (t := {ω | err ω ≠ 0}) ?_ (ae_iff.mp hae0)
        intro ω hω
        simp only [goodErrorEvent, Set.mem_compl_iff, Set.mem_setOf_eq, not_le] at hω
        rw [← hU0'] at hω; simp only [zero_div] at hω
        exact ne_of_gt hω
      rw [measureReal_def, hnull]; simp; exact le_of_lt hδ0
    · -- `U > 0`: genuine Markov inequality at level `U/δ`.
      have hmarkov := mul_meas_ge_le_integral_of_nonneg hae_nonneg herr_int (U / δ)
      have hεpos : 0 < U / δ := div_pos hUpos hδ0
      have hmU : (U / δ) * μ.real {ω | U / δ ≤ err ω} ≤ U := le_trans hmarkov hU
      have hle : μ.real {ω | U / δ ≤ err ω} ≤ δ := by
        have key : (U / δ) * δ = U := by field_simp
        have : (U / δ) * μ.real {ω | U / δ ≤ err ω} ≤ (U / δ) * δ := by rw [key]; exact hmU
        exact le_of_mul_le_mul_left this hεpos
      exact le_trans (measureReal_mono hsub) hle
  have huniv : μ.real (Set.univ : Set Ω) = 1 := by simp [measureReal_def]
  have hcompl : μ.real (goodErrorEvent err U δ)ᶜ = 1 - μ.real (goodErrorEvent err U δ) := by
    have := measureReal_add_measureReal_compl (μ := μ) hmeas_s
    rw [huniv] at this; linarith
  have hgood : (1 : ℝ) - δ ≤ μ.real (goodErrorEvent err U δ) := by
    rw [hcompl] at hcompl_le; linarith
  calc ENNReal.ofReal (1 - δ) ≤ ENNReal.ofReal (μ.real (goodErrorEvent err U δ)) :=
        ENNReal.ofReal_le_ofReal hgood
    _ = μ (goodErrorEvent err U δ) := by
        rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]

/-- Safe corrected scaling theorem: expected total-error control yields a high-probability F1 lower guarantee.

This theorem intentionally does not claim an F1 upper decay rate.

Correction to the originally stated lemma: an `Integrable (fun ω => fp ω + fn ω) μ`
hypothesis is required for the underlying Markov step (see `prob_goodErrorEvent`). -/
theorem high_probability_f1_lower
    [IsProbabilityMeasure μ]
    (s U δ : ℝ)
    (fp fn : Ω → ℝ)
    (hfp_meas : Measurable fp) (hfn_meas : Measurable fn)
    (herr_int : Integrable (fun ω => fp ω + fn ω) μ)
    (hfp0 : ∀ ω, 0 ≤ fp ω) (hfn0 : ∀ ω, 0 ≤ fn ω)
    (hfn_le : ∀ ω, fn ω ≤ s)
    (herr : ∫ ω, (fp ω + fn ω) ∂μ ≤ U)
    (hs : 0 < s) (hU0 : 0 ≤ U)
    (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hsmall : U / δ < s) :
    μ {ω | f1Counts (s - fn ω) (fp ω) (fn ω) ≥
      2 * (s - U / δ) / (2 * s + U / δ)} ≥
      ENNReal.ofReal (1 - δ) := by
  set err : Ω → ℝ := fun ω => fp ω + fn ω with herr_def
  have herr_meas : Measurable err := hfp_meas.add hfn_meas
  have herr_nonneg : ∀ ω, 0 ≤ err ω := fun ω => add_nonneg (hfp0 ω) (hfn0 ω)
  have hbase := prob_goodErrorEvent μ err U δ herr_meas herr_int herr_nonneg herr hδ0 hδ1 hU0
  -- The good-error event is contained in the desired F1-lower event.
  have hsubset : goodErrorEvent err U δ ⊆
      {ω | f1Counts (s - fn ω) (fp ω) (fn ω) ≥ 2 * (s - U / δ) / (2 * s + U / δ)} := by
    intro ω hω
    simp only [goodErrorEvent, Set.mem_setOf_eq] at hω
    exact f1_lower_of_total_error s (fp ω) (fn ω) (U / δ)
      hs (hfp0 ω) (hfn0 ω) (hfn_le ω) hω hsmall
  exact le_trans hbase (measure_mono hsubset)

end RecoveryCore
