import Mathlib
import RecoveryFormal.OracleDecisionTransfer

open MeasureTheory ProbabilityTheory

namespace RecoveryFormal

/-- Deterministic event inclusion reused for a finite query family.

The graph-output mismatch event is contained in the union of query-decision
(coordinate) error events. This is the logical spine of the argument: it holds
pointwise, with **no** independence or measurability assumption. -/
theorem search_failure_event_subset
    {Ω ι O : Type*} [Fintype ι]
    (A : (ι → Bool) → O)
    (truth estimate : Ω → ι → Bool) :
    {ω | A (estimate ω) ≠ A (truth ω)} ⊆
      ⋃ i, {ω | estimate ω i ≠ truth ω i} :=
  output_error_subset_coordinate_errors A estimate truth

/-- Finite measure union bound applied to the graph-failure event.

Under *any* measure (in particular any probability measure), the probability of
the graph-output mismatch is bounded by the **sum** of the querywise decision
error probabilities. This uses only monotonicity and countable subadditivity of
the (outer) measure — no independence assumption is made. -/
theorem search_failure_prob_le_sum
    {Ω ι O : Type*} [Fintype ι] [MeasurableSpace Ω]
    (μ : Measure Ω)
    (A : (ι → Bool) → O)
    (truth estimate : Ω → ι → Bool) :
    μ {ω | A (estimate ω) ≠ A (truth ω)} ≤
      ∑ i, μ {ω | estimate ω i ≠ truth ω i} :=
  calc
    μ {ω | A (estimate ω) ≠ A (truth ω)}
        ≤ μ (⋃ i, {ω | estimate ω i ≠ truth ω i}) :=
          measure_mono (search_failure_event_subset A truth estimate)
    _ ≤ ∑ i, μ {ω | estimate ω i ≠ truth ω i} :=
          measure_iUnion_fintype_le μ _

/-- Elementary event decomposition: any event `E` is covered by its restriction
to a region `B` together with the complement of `B`. Needs no measurability. -/
theorem measure_le_inter_add_compl
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (E B : Set Ω) :
    μ E ≤ μ (E ∩ B) + μ Bᶜ := by
  calc
    μ E ≤ μ ((E ∩ B) ∪ Bᶜ) := by
          apply measure_mono
          intro x hx
          by_cases hb : x ∈ B
          · exact Or.inl ⟨hx, hb⟩
          · exact Or.inr hb
    _ ≤ μ (E ∩ B) + μ Bᶜ := measure_union_le _ _

/-- A conditional-probability bound transfers to a joint-probability bound.

If the error event `E` has conditional probability at most `ε` given the
"enough effective samples" region `B` (with `B` measurable and having positive,
finite mass — the **denominator condition**), then the joint mass of error and
`B` is at most `μ B * ε`. -/
theorem measure_inter_le_of_cond_le
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (E B : Set Ω)
    (hB : MeasurableSet B) (hpos : μ B ≠ 0) (hfin : μ B ≠ ⊤)
    {ε : ENNReal} (hcond : (μ[E | B]) ≤ ε) :
    μ (E ∩ B) ≤ μ B * ε := by
  have hcode : (μ[E | B]) = (μ B)⁻¹ * μ (E ∩ B) := by
    rw [cond_apply hB, Set.inter_comm]
  have hkey : μ (E ∩ B) = μ B * (μ[E | B]) := by
    rw [hcode, ← mul_assoc, ENNReal.mul_inv_cancel hpos hfin, one_mul]
  calc
    μ (E ∩ B) = μ B * (μ[E | B]) := hkey
    _ ≤ μ B * ε := by gcongr

/-- **Effective-sample decomposition.**

For a probability measure `μ`, if the error event `E` has conditional
probability at most `ε` given the region `B = {N_q ≥ m_q}` of "enough effective
samples", then the (unconditional) error probability is bounded by
`ε + P(N_q < m_q)`, where `Bᶜ = {N_q < m_q}`.

Assumptions used:
* `IsProbabilityMeasure μ` — needed so `μ B ≤ 1` (hence `μ B * ε ≤ ε`);
* `hB : MeasurableSet B` — the denominator/conditioning set is measurable;
* `hpos : μ B ≠ 0` — the denominator condition (positive conditioning mass). -/
theorem error_prob_le_cond_add_deficient
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (E B : Set Ω) (hB : MeasurableSet B) (hpos : μ B ≠ 0)
    {ε : ENNReal} (hcond : (μ[E | B]) ≤ ε) :
    μ E ≤ ε + μ Bᶜ := by
  have hfin : μ B ≠ ⊤ := measure_ne_top μ B
  have hjoint : μ (E ∩ B) ≤ μ B * ε :=
    measure_inter_le_of_cond_le μ E B hB hpos hfin hcond
  have hle1 : μ B ≤ 1 := prob_le_one
  have hmul : μ B * ε ≤ ε := by
    calc μ B * ε ≤ 1 * ε := by gcongr
      _ = ε := one_mul ε
  calc
    μ E ≤ μ (E ∩ B) + μ Bᶜ := measure_le_inter_add_compl μ E B
    _ ≤ μ B * ε + μ Bᶜ := by gcongr
    _ ≤ ε + μ Bᶜ := by gcongr

/-- **Grand bound: querywise CI errors propagate to search-recovery failure.**

Combining the deterministic event inclusion, the finite union bound, and the
effective-sample decomposition across the finite query family: the graph-output
mismatch probability is bounded by the sum over queries of
`ε_q + P(N_q < m_q)`, with **no independence assumption**.

For each query `i`:
* `B i := {ω | m i ≤ N i ω}` is the "enough effective samples" region;
* `Bᶜ = {ω | N i ω < m i}` is the effective-sample deficiency event;
* `hcond i` bounds the conditional error probability by `ε i`;
* `hB i`, `hpos i` are the measurability and denominator conditions. -/
theorem search_failure_prob_le_sum_effective
    {Ω ι O : Type*} [Fintype ι] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : (ι → Bool) → O)
    (truth estimate : Ω → ι → Bool)
    (N : ι → Ω → ℕ) (m : ι → ℕ) (ε : ι → ENNReal)
    (hB : ∀ i, MeasurableSet {ω | m i ≤ N i ω})
    (hpos : ∀ i, μ {ω | m i ≤ N i ω} ≠ 0)
    (hcond : ∀ i,
      (μ[{ω | estimate ω i ≠ truth ω i} | {ω | m i ≤ N i ω}]) ≤ ε i) :
    μ {ω | A (estimate ω) ≠ A (truth ω)} ≤
      ∑ i, (ε i + μ {ω | N i ω < m i}) := by
  refine (search_failure_prob_le_sum μ A truth estimate).trans ?_
  refine Finset.sum_le_sum ?_
  intro i _
  have hcompl : {ω | m i ≤ N i ω}ᶜ = {ω | N i ω < m i} := by
    ext ω; simp [not_le]
  have := error_prob_le_cond_add_deficient μ
    {ω | estimate ω i ≠ truth ω i} {ω | m i ≤ N i ω} (hB i) (hpos i) (hcond i)
  rwa [hcompl] at this

#print axioms search_failure_event_subset
#print axioms search_failure_prob_le_sum
#print axioms measure_le_inter_add_compl
#print axioms measure_inter_le_of_cond_le
#print axioms error_prob_le_cond_add_deficient
#print axioms search_failure_prob_le_sum_effective

end RecoveryFormal
