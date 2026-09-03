import Mathlib
import RecoveryFormal.GaussianPreservingSelection
import RecoveryFormal.SelectedLawOracleTransfer
import RecoveryFormal.RetainedRowsIID
import RecoveryFormal.ConditionalTypeI
import RecoveryFormal.ConditionalAlternativeError
import RecoveryFormal.OracleDecisionTransfer
import RecoveryFormal.RetainedCountConcentration
import RecoveryFormal.SearchErrorUnionBound
import RecoveryFormal.ExactRecoveryF1Bridge

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal
namespace RecoveryFormal
namespace EndToEndRecovery
open RecoveryCore

/-- A finite prespecified family of CI queries. -/
abbrev QueryIndex (k : ℕ) := Fin k
/-- The complete-data oracle decision vector. -/
abbrev OracleVector (ι : Type*) := ι → Bool
/-- A random implemented decision vector. -/
abbrev ImplementedVector (Ω ι : Type*) := Ω → ι → Bool
/-- A deterministic skeleton-search map. -/
abbrev SearchMap (ι G : Type*) := (ι → Bool) → G
/-- The graph produced from a decision vector. -/
def graphOutput {ι G : Type*} (search : SearchMap ι G) (d : ι → Bool) : G := search d
/-- Exact graph recovery as an event in the experiment sample space. -/
def exactRecoveryEvent {Ω ι G : Type*} (search : SearchMap ι G)
    (estimated : ImplementedVector Ω ι) (truth : G) : Set Ω :=
  {ω | graphOutput search (estimated ω) = truth}

/-- Abstract finite-query composition.  Each coordinate error is split into its
conditional sufficient-sample error and its insufficient-retention probability;
The recovery-composition results then propagate coordinate-wise bounds through the deterministic search.
No independence between query errors is assumed. -/
theorem search_failure_le_query_bounds
    {Ω ι G : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (search : SearchMap ι G) (oracle : OracleVector ι)
    (estimated : ImplementedVector Ω ι) (truth : G)
    (horacle : search oracle = truth)
    (sufficient : ι → Set Ω) (epsilon deficient : ι → ℝ≥0∞)
    (hmeas : ∀ q, MeasurableSet (sufficient q))
    (hpos : ∀ q, μ (sufficient q) ≠ 0)
    (hconditional : ∀ q,
      (μ[{ω | estimated ω q ≠ oracle q} | sufficient q]) ≤ epsilon q)
    (hdeficient : ∀ q, μ (sufficient q)ᶜ ≤ deficient q) :
    μ {ω | graphOutput search (estimated ω) ≠ truth} ≤
      ∑ q, (epsilon q + deficient q) := by
  rw [show {ω | graphOutput search (estimated ω) ≠ truth} =
      {ω | search (estimated ω) ≠ search oracle} by ext ω; simp [graphOutput, horacle]]
  refine (search_failure_prob_le_sum μ search (fun _ => oracle) estimated).trans ?_
  apply Finset.sum_le_sum
  intro q _
  exact (error_prob_le_cond_add_deficient μ
    {ω | estimated ω q ≠ oracle q} (sufficient q) (hmeas q) (hpos q)
    (hconditional q)).trans (add_le_add_right (hdeficient q) (epsilon q))

/-- retained-count concentration instantiated query by query at the exact threshold
`(1-eta) * n * q_q`; query-specific retention probabilities are preserved. -/
theorem concrete_search_failure_chernoff
    {Ω ι G : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (n : ℕ) (retained : ι → Fin n → Ω → Bool) (retentionProb : ι → ℝ≥0)
    (eta : ℝ) (heta0 : 0 < eta) (heta1 : eta < 1)
    (hmeasRetained : ∀ q r, Measurable (retained q r))
    (hindepRows : ∀ q, iIndepFun (retained q) μ)
    (hmarginal : ∀ q r, μ {ω | retained q r ω = true} = (retentionProb q : ℝ≥0∞))
    (hprob : ∀ q, retentionProb q ≤ 1)
    (hmeasEnough : ∀ q, MeasurableSet {ω | (1 - eta) * n * (retentionProb q : ℝ) <
      (retainedCountAt (retained q) ω : ℝ)})
    (search : SearchMap ι G) (oracle : OracleVector ι)
    (estimated : ImplementedVector Ω ι) (truth : G)
    (markov faithful depthSeparator : Prop)
    (hmarkov : markov) (hfaithful : faithful) (hdepthSeparator : depthSeparator)
    (horacleCorrect : markov → faithful → depthSeparator → search oracle = truth)
    (epsilon : ι → ℝ≥0∞)
    (rejectionEvent failureEvent : ι → Set Ω)
    (hrejection : ∀ q ω, estimated ω q = true ↔ ω ∈ rejectionEvent q)
    (hfailure : ∀ q ω, estimated ω q = false ↔ ω ∈ failureEvent q)
    (hnullCalibration : ∀ q, oracle q = false →
      (μ[rejectionEvent q | {ω | (1 - eta) * n * (retentionProb q : ℝ) <
        (retainedCountAt (retained q) ω : ℝ)}]) ≤ epsilon q)
    (haltCalibration : ∀ q, oracle q = true →
      (μ[failureEvent q | {ω | (1 - eta) * n * (retentionProb q : ℝ) <
        (retainedCountAt (retained q) ω : ℝ)}]) ≤ epsilon q)
    (hpositiveEnough : ∀ q,
      μ {ω | (1 - eta) * n * (retentionProb q : ℝ) <
        (retainedCountAt (retained q) ω : ℝ)} ≠ 0) :
    μ {ω | graphOutput search (estimated ω) ≠ truth} ≤
      ∑ q, (epsilon q + ENNReal.ofReal
        (Real.exp (-(eta ^ 2 * n * (retentionProb q : ℝ)) / 2))) := by
  apply search_failure_le_query_bounds μ search oracle estimated truth
    (horacleCorrect hmarkov hfaithful hdepthSeparator)
    (fun q => {ω | (1 - eta) * n * (retentionProb q : ℝ) <
      (retainedCountAt (retained q) ω : ℝ)}) epsilon
    (fun q => ENNReal.ofReal (Real.exp (-(eta ^ 2 * n * (retentionProb q : ℝ)) / 2)))
  · exact hmeasEnough
  · exact hpositiveEnough
  · intro q
    cases hq : oracle q
    · exact conditional_typeI μ (estimated · q) _ _ (epsilon q)
        (hrejection q) (hnullCalibration q hq)
    · exact conditional_alternative_error μ (estimated · q) _ _ (epsilon q)
        (hfailure q) (haltCalibration q hq)
  · intro q
    have heq : {ω | (1 - eta) * n * (retentionProb q : ℝ) <
        (retainedCountAt (retained q) ω : ℝ)}ᶜ =
        {ω | (retainedCountAt (retained q) ω : ℝ) ≤
          (1 - eta) * n * (retentionProb q : ℝ)} := by
      ext ω; simp [not_lt]
    rw [heq]
    exact retainedCount_chernoff (hmeasRetained q) (hindepRows q) (hmarginal q)
      (hprob q) eta heta0 heta1

/-- A finite-sum failure bound implies the `1-delta` exact-recovery probability. -/
theorem exact_recovery_prob_ge_one_sub_delta
    {Ω ι G : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (search : SearchMap ι G) (estimated : ImplementedVector Ω ι) (truth : G)
    (bound : ℝ≥0∞) (hfail : μ {ω | graphOutput search (estimated ω) ≠ truth} ≤ bound)
    (delta : ℝ) (hdelta0 : 0 ≤ delta) (hbound : bound ≤ ENNReal.ofReal delta)
    (hmeasExact : MeasurableSet (exactRecoveryEvent search estimated truth)) :
    μ (exactRecoveryEvent search estimated truth) ≥ ENNReal.ofReal (1 - delta) := by
  have hcompl : (exactRecoveryEvent search estimated truth)ᶜ =
      {ω | graphOutput search (estimated ω) ≠ truth} := by
    ext ω; simp [exactRecoveryEvent, graphOutput]
  rw [ENNReal.ofReal_sub 1 hdelta0, ENNReal.ofReal_one]
  have hfailure : μ (exactRecoveryEvent search estimated truth)ᶜ ≤ ENNReal.ofReal delta := by
    rw [hcompl]
    exact hfail.trans hbound
  have hc := measure_compl hmeasExact.compl
    (measure_ne_top μ (exactRecoveryEvent search estimated truth)ᶜ)
  simp only [compl_compl, measure_univ] at hc
  rw [hc]
  exact tsub_le_tsub_left hfailure 1

/-- Exact recovery also gives `F1=1` with the same probability. -/
theorem f1_one_prob_ge_one_sub_delta
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (E : Set Ω) (delta s : ℝ) (hs : 0 < s)
    (fp fn : Ω → ℝ) (hexact : ∀ ω ∈ E, fp ω = 0 ∧ fn ω = 0)
    (hrec : μ E ≥ ENNReal.ofReal (1 - delta)) :
    μ {ω | f1Counts (s - fn ω) (fp ω) (fn ω) = 1} ≥
      ENNReal.ofReal (1 - delta) := by
  refine hrec.trans (measure_mono ?_)
  intro ω hω
  obtain ⟨hfp, hfn⟩ := hexact ω hω
  simp only [Set.mem_setOf_eq, hfp, hfn, sub_zero]
  exact exact_recovery_f1_one s hs

/-- exact-recovery/F1 bridge composition: exact recovery with probability `1-delta` yields expected
F1 at least `1-delta` under its standard nonempty-truth and integrability premises. -/
theorem expected_f1_ge_one_sub_delta
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (s delta : ℝ) (fp fn : Ω → ℝ) (E : Set Ω)
    (hs : 0 < s) (hfp_meas : Measurable fp) (hfn_meas : Measurable fn)
    (hfp0 : ∀ ω, 0 ≤ fp ω) (hfn0 : ∀ ω, 0 ≤ fn ω)
    (hfn_le : ∀ ω, fn ω ≤ s)
    (hint : Integrable (fun ω => f1Counts (s - fn ω) (fp ω) (fn ω)) μ)
    (hexact : ∀ ω ∈ E, fp ω = 0 ∧ fn ω = 0)
    (hE : μ E ≥ ENNReal.ofReal (1 - delta)) (hdelta0 : 0 ≤ delta)
    (hdelta1 : delta ≤ 1) :
    ∫ ω, f1Counts (s - fn ω) (fp ω) (fn ω) ∂μ ≥ 1 - delta :=
  expected_f1_ge_of_exact_recovery μ s delta fp fn hs hfp_meas hfn_meas
    hfp0 hfn0 hfn_le hint E hexact hE hdelta0 hdelta1

/-- The three advertised `1-delta` consequences, packaged together from one
explicit failure bound. -/
theorem recovery_f1_corollaries
    {Ω ι G : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (search : SearchMap ι G) (estimated : ImplementedVector Ω ι) (truth : G)
    (bound : ℝ≥0∞) (delta s : ℝ) (hdelta0 : 0 ≤ delta) (hdelta1 : delta ≤ 1)
    (hbound : bound ≤ ENNReal.ofReal delta)
    (hfail : μ {ω | graphOutput search (estimated ω) ≠ truth} ≤ bound)
    (hmeasExact : MeasurableSet (exactRecoveryEvent search estimated truth))
    (fp fn : Ω → ℝ) (hs : 0 < s)
    (hfp_meas : Measurable fp) (hfn_meas : Measurable fn)
    (hfp0 : ∀ ω, 0 ≤ fp ω) (hfn0 : ∀ ω, 0 ≤ fn ω)
    (hfn_le : ∀ ω, fn ω ≤ s)
    (hint : Integrable (fun ω => f1Counts (s - fn ω) (fp ω) (fn ω)) μ)
    (hexact : ∀ ω ∈ exactRecoveryEvent search estimated truth,
      fp ω = 0 ∧ fn ω = 0) :
    μ (exactRecoveryEvent search estimated truth) ≥ ENNReal.ofReal (1 - delta) ∧
    μ {ω | f1Counts (s - fn ω) (fp ω) (fn ω) = 1} ≥ ENNReal.ofReal (1 - delta) ∧
    ∫ ω, f1Counts (s - fn ω) (fp ω) (fn ω) ∂μ ≥ 1 - delta := by
  have hrec := exact_recovery_prob_ge_one_sub_delta μ search estimated truth bound
    hfail delta hdelta0 hbound hmeasExact
  exact ⟨hrec,
    f1_one_prob_ge_one_sub_delta μ _ delta s hs fp fn hexact hrec,
    expected_f1_ge_one_sub_delta μ s delta fp fn _ hs hfp_meas hfn_meas
      hfp0 hfn0 hfn_le hint hexact hrec hdelta0 hdelta1⟩

#print axioms search_failure_le_query_bounds
#print axioms concrete_search_failure_chernoff
#print axioms exact_recovery_prob_ge_one_sub_delta
#print axioms f1_one_prob_ge_one_sub_delta
#print axioms expected_f1_ge_one_sub_delta
#print axioms recovery_f1_corollaries
end EndToEndRecovery
end RecoveryFormal
