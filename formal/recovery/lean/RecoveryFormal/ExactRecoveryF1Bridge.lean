import Mathlib
import RecoveryCore.Basic
import RecoveryCore.DeterministicF1

open MeasureTheory ProbabilityTheory

namespace RecoveryFormal
open RecoveryCore

/-- Zero false positives and false negatives yield perfect F1 for a nonempty truth set. -/
theorem exact_recovery_f1_one (s : ℝ) (hs : 0 < s) :
    f1Counts s 0 0 = 1 := by
  have hden : 2 * s + 0 + 0 ≠ 0 := by linarith
  rw [f1Counts_eq s 0 0 hden,
    show (2:ℝ) * s + 0 + 0 = 2 * s by ring, div_self (by linarith : (2:ℝ) * s ≠ 0)]

/-- A bounded score equal to one on an event of probability at least 1-δ has expectation at least 1-δ.

The two hypotheses `hscore1 : ∀ ω, score ω ≤ 1` and `hδ0 : 0 ≤ δ` encode the stated result
assumptions that F1 lies in `[0,1]` and that `δ` is a probability level.  They are
retained because they are part of the scientific statement, even though the proof
below does not need them (the argument only uses `score ≥ 0`, `score = 1` on `E`,
and `δ ≤ 1`). -/
theorem expectation_ge_of_perfect_event
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (score : Ω → ℝ) (E : Set Ω) (δ : ℝ)
    (hscore_meas : Measurable score)
    (hscore_int : Integrable score μ)
    (hscore0 : ∀ ω, 0 ≤ score ω)
    (hscore1 : ∀ ω, score ω ≤ 1)
    (hperfect : ∀ ω ∈ E, score ω = 1)
    (hE : μ E ≥ ENNReal.ofReal (1 - δ))
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    ∫ ω, score ω ∂μ ≥ 1 - δ := by
  -- `F` is the *measurable* event where the score attains its maximum value `1`.
  -- It contains `E`, so it also has probability at least `1-δ`, and it lets us
  -- avoid assuming that `E` itself is measurable.
  set F : Set Ω := {ω | (1:ℝ) ≤ score ω} with hF_def
  have hF_meas : MeasurableSet F := measurableSet_le measurable_const hscore_meas
  have hEF : E ⊆ F := by
    intro ω hω
    simp only [hF_def, Set.mem_setOf_eq]
    exact (hperfect ω hω).ge
  have hμF : ENNReal.ofReal (1 - δ) ≤ μ F := le_trans hE (measure_mono hEF)
  -- The score dominates the indicator of `F` pointwise.
  have hind_le : ∀ ω, F.indicator (fun _ => (1:ℝ)) ω ≤ score ω := by
    intro ω
    by_cases h : ω ∈ F
    · rw [Set.indicator_of_mem h]; exact h
    · rw [Set.indicator_of_notMem h]; exact hscore0 ω
  have hint_ind : Integrable (F.indicator (fun _ => (1:ℝ))) μ :=
    (integrable_const (1:ℝ)).indicator hF_meas
  have hmono : ∫ ω, F.indicator (fun _ => (1:ℝ)) ω ∂μ ≤ ∫ ω, score ω ∂μ :=
    integral_mono hint_ind hscore_int hind_le
  have hint_eq : ∫ ω, F.indicator (fun _ => (1:ℝ)) ω ∂μ = μ.real F := by
    rw [integral_indicator hF_meas, setIntegral_const]; simp
  have hreal : (1 : ℝ) - δ ≤ μ.real F := by
    have h1 : (ENNReal.ofReal (1 - δ)).toReal ≤ (μ F).toReal :=
      ENNReal.toReal_mono (measure_ne_top μ F) hμF
    rw [ENNReal.toReal_ofReal (by linarith)] at h1
    exact h1
  rw [hint_eq] at hmono
  linarith

/-- The guarded F1 score always lies in `[0,1]` for nonnegative confusion counts. -/
theorem f1Counts_mem_unit (tp fp fn : ℝ) (htp : 0 ≤ tp) (hfp : 0 ≤ fp) (hfn : 0 ≤ fn) :
    0 ≤ f1Counts tp fp fn ∧ f1Counts tp fp fn ≤ 1 := by
  unfold f1Counts
  split_ifs with h
  · exact ⟨le_refl 0, zero_le_one⟩
  · have hden : 0 < 2 * tp + fp + fn := lt_of_le_of_ne (by linarith) (Ne.symm h)
    exact ⟨div_nonneg (by linarith) (by linarith), by rw [div_le_one hden]; linarith⟩

/-- Combined bridge: if exact graph recovery (`fp = fn = 0`) holds on an event of
probability at least `1-δ`, then the expected F1 score is at least `1-δ`.

This composes `exact_recovery_f1_one` (exact recovery forces `F1 = 1`) with
`expectation_ge_of_perfect_event` (a `[0,1]`-valued score equal to `1` on a
`(1-δ)`-probability event has expectation at least `1-δ`).  The F1 random variable
is the querywise/pointwise count-based score `f1Counts (s - fn ω) (fp ω) (fn ω)`
used by the deterministic F1 lower theorem `f1_lower_of_total_error`.  No F1 upper
decay rate is claimed. -/
theorem expected_f1_ge_of_exact_recovery
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (s δ : ℝ) (fp fn : Ω → ℝ)
    (hs : 0 < s)
    (hfp_meas : Measurable fp) (hfn_meas : Measurable fn)
    (hfp0 : ∀ ω, 0 ≤ fp ω) (hfn0 : ∀ ω, 0 ≤ fn ω)
    (hfn_le : ∀ ω, fn ω ≤ s)
    (hf1_int : Integrable (fun ω => f1Counts (s - fn ω) (fp ω) (fn ω)) μ)
    (E : Set Ω)
    (hexact : ∀ ω ∈ E, fp ω = 0 ∧ fn ω = 0)
    (hE : μ E ≥ ENNReal.ofReal (1 - δ))
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    ∫ ω, f1Counts (s - fn ω) (fp ω) (fn ω) ∂μ ≥ 1 - δ := by
  have hf1_meas : Measurable (fun ω => f1Counts (s - fn ω) (fp ω) (fn ω)) := by
    unfold f1Counts
    apply Measurable.ite
    · exact measurableSet_eq_fun (by fun_prop) measurable_const
    · exact measurable_const
    · fun_prop
  refine expectation_ge_of_perfect_event μ _ E δ hf1_meas hf1_int
    (fun ω => (f1Counts_mem_unit _ _ _ (by linarith [hfn_le ω]) (hfp0 ω) (hfn0 ω)).1)
    (fun ω => (f1Counts_mem_unit _ _ _ (by linarith [hfn_le ω]) (hfp0 ω) (hfn0 ω)).2)
    ?_ hE hδ0 hδ1
  intro ω hω
  obtain ⟨hfpω, hfnω⟩ := hexact ω hω
  rw [hfpω, hfnω, sub_zero]
  exact exact_recovery_f1_one s hs

#print axioms exact_recovery_f1_one
#print axioms expectation_ge_of_perfect_event
#print axioms f1Counts_mem_unit
#print axioms expected_f1_ge_of_exact_recovery

end RecoveryFormal
