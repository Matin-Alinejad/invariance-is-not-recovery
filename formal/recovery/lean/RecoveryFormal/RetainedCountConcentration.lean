import Mathlib
import RecoveryFormal.BinomialChernoff

open MeasureTheory ProbabilityTheory Finset
open scoped NNReal ENNReal

namespace RecoveryFormal

/-- Retained count for a finite row index set: the number of retained rows. -/
def retainedCount {n : ℕ} (C : Fin n → Bool) : ℕ :=
  ∑ r, if C r then 1 else 0

/-- Elementary bound needed by the probabilistic development. -/
theorem retainedCount_le {n : ℕ} (C : Fin n → Bool) :
    retainedCount C ≤ n := by
  calc retainedCount C ≤ ∑ _r : Fin n, 1 := by
        apply Finset.sum_le_sum; intro i _; split <;> simp
    _ = n := by simp

/-- The retained count equals the number of coordinates that are retained. -/
lemma retainedCount_eq_card {n : ℕ} (C : Fin n → Bool) :
    retainedCount C = (univ.filter (fun r => C r = true)).card := by
  rw [Finset.card_filter, retainedCount]

/-- Pointwise retained count of a random Boolean row configuration. -/
def retainedCountAt {Ω : Type*} {n : ℕ} (C : Fin n → Ω → Bool) (ω : Ω) : ℕ :=
  retainedCount (fun r => C r ω)

section Law

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {n : ℕ} {C : Fin n → Ω → Bool} {q : ℝ≥0}

/-- The event that row `r` is not retained has probability `1 - q`. -/
lemma measure_row_false (hmeas : ∀ r, Measurable (C r))
    (hmarg : ∀ r, μ {ω | C r ω = true} = (q : ℝ≥0∞)) (r : Fin n) :
    μ {ω | C r ω = false} = 1 - (q : ℝ≥0∞) := by
  have hm : MeasurableSet {ω | C r ω = true} := (hmeas r) (measurableSet_singleton true)
  have hcompl : {ω | C r ω = false} = {ω | C r ω = true}ᶜ := by
    ext ω; cases h : C r ω <;> simp [h]
  rw [hcompl, measure_compl hm (measure_ne_top _ _), measure_univ, hmarg r]

/-- Probability of a fixed retention pattern `S`: rows in `S` retained, the rest
not. By independence this is `q^{|S|} (1-q)^{n-|S|}`. -/
lemma measure_patternEvent (hmeas : ∀ r, Measurable (C r))
    (hindep : iIndepFun C μ)
    (hmarg : ∀ r, μ {ω | C r ω = true} = (q : ℝ≥0∞))
    (S : Finset (Fin n)) :
    μ {ω | ∀ r, C r ω = decide (r ∈ S)}
      = (q : ℝ≥0∞) ^ S.card * (1 - (q : ℝ≥0∞)) ^ (n - S.card) := by
  have hrw : {ω | ∀ r, C r ω = decide (r ∈ S)} = ⋂ r, (C r) ⁻¹' {decide (r ∈ S)} := by
    ext ω; simp [Set.mem_iInter, Set.mem_preimage]
  rw [hrw, hindep.meas_iInter
      (fun r => ⟨{decide (r ∈ S)}, measurableSet_singleton _, rfl⟩)]
  have hfac : ∀ r, μ ((C r) ⁻¹' {decide (r ∈ S)})
      = if r ∈ S then (q : ℝ≥0∞) else (1 - (q : ℝ≥0∞)) := by
    intro r
    by_cases hr : r ∈ S
    · simp only [hr, decide_true, if_true]; exact hmarg r
    · simp only [hr, decide_false, if_false]; exact measure_row_false hmeas hmarg r
  rw [Finset.prod_congr rfl (fun r _ => hfac r), Finset.prod_ite]
  simp only [Finset.prod_const]
  congr 1
  · congr 1
    rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
  · congr 1
    have hset : (univ.filter (fun r => ¬ r ∈ S)) = univ \ S := by
      ext r; simp [Finset.mem_sdiff]
    rw [hset, Finset.card_univ_diff, Fintype.card_fin]

omit [MeasurableSpace Ω] in
/-- The event `{N = k}` is the disjoint union over `k`-subsets `S` of the
corresponding retention patterns. -/
lemma retainedCount_eq_biUnion (k : ℕ) :
    {ω | retainedCountAt C ω = k}
      = ⋃ S ∈ powersetCard k (univ : Finset (Fin n)),
          {ω | ∀ r, C r ω = decide (r ∈ S)} := by
  ext ω
  simp only [Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_powersetCard, Finset.subset_univ,
    true_and, exists_prop]
  rw [retainedCountAt, retainedCount_eq_card]
  constructor
  · intro h
    refine ⟨univ.filter (fun r => C r ω = true), h, ?_⟩
    intro r
    by_cases hr : C r ω = true <;> simp [hr, Finset.mem_filter]
  · rintro ⟨S, hcard, hS⟩
    rw [← hcard]
    congr 1
    ext r
    rw [Finset.mem_filter]
    simp only [Finset.mem_univ, true_and, hS r, decide_eq_true_eq]

/-- The event `{N = k}` is measurable. -/
lemma measurableSet_retainedCount_eq (hmeas : ∀ r, Measurable (C r)) (k : ℕ) :
    MeasurableSet {ω | retainedCountAt C ω = k} := by
  rw [retainedCount_eq_biUnion]
  refine Finset.measurableSet_biUnion _ (fun S _ => ?_)
  have hrw : {ω | ∀ r, C r ω = decide (r ∈ S)} = ⋂ r, {ω | C r ω = decide (r ∈ S)} := by
    ext ω; simp [Set.mem_iInter]
  rw [hrw]
  exact MeasurableSet.iInter (fun r => (hmeas r) (measurableSet_singleton _))

/-- **Binomial law of the retained count.**
If the row-retention indicators `C r` are independent (iid, with common joint
retention probability `q`) and each measurable, then the retained count `N_J`
follows the binomial law `Binomial n q`: for every `k`,
`μ {N = k} = (n choose k) qᵏ (1-q)ⁿ⁻ᵏ`.

(The constraint `q ≤ 1` that makes `q` a genuine binomial parameter is automatic
here: it follows from `hmarg` together with `μ` being a probability measure, so it
is not needed as a separate hypothesis for this identity. The real-valued and
Chernoff forms below take it explicitly where the real arithmetic requires it.) -/
theorem retainedCount_binomial
    (hmeas : ∀ r, Measurable (C r))
    (hindep : iIndepFun C μ)
    (hmarg : ∀ r, μ {ω | C r ω = true} = (q : ℝ≥0∞))
    (k : ℕ) :
    μ {ω | retainedCountAt C ω = k}
      = (n.choose k : ℝ≥0∞) * (q : ℝ≥0∞) ^ k * (1 - (q : ℝ≥0∞)) ^ (n - k) := by
  rw [retainedCount_eq_biUnion, measure_biUnion_finset]
  · rw [Finset.sum_congr rfl fun S hS => by
        rw [measure_patternEvent hmeas hindep hmarg, (Finset.mem_powersetCard.mp hS).2]]
    rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    ring
  · intro a _ b _ hab
    simp only [Function.onFun, Set.disjoint_left, Set.mem_setOf_eq]
    rintro ω hωa hωb
    apply hab; ext r
    exact decide_eq_decide.mp ((hωa r).symm.trans (hωb r))
  · intro S _
    have hset : {ω | ∀ r, C r ω = decide (r ∈ S)} = ⋂ r, (C r) ⁻¹' {decide (r ∈ S)} := by
      ext ω; simp [Set.mem_iInter, Set.mem_preimage]
    rw [hset]
    exact MeasurableSet.iInter (fun r => (hmeas r) (measurableSet_singleton _))

/-- Binomial law, phrased with a real-valued mass through `ENNReal.ofReal`. -/
theorem retainedCount_binomial_ofReal
    (hmeas : ∀ r, Measurable (C r))
    (hindep : iIndepFun C μ)
    (hmarg : ∀ r, μ {ω | C r ω = true} = (q : ℝ≥0∞))
    (hq : q ≤ 1) (k : ℕ) :
    μ {ω | retainedCountAt C ω = k}
      = ENNReal.ofReal ((n.choose k : ℝ) * (q : ℝ) ^ k * (1 - (q : ℝ)) ^ (n - k)) := by
  rw [retainedCount_binomial hmeas hindep hmarg k]
  have hq' : (q : ℝ) ≤ 1 := by exact_mod_cast hq
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_natCast, ENNReal.ofReal_pow (by positivity),
      ENNReal.ofReal_pow (by linarith), ENNReal.ofReal_coe_nnreal,
      ENNReal.ofReal_sub _ (by positivity), ENNReal.ofReal_one, ENNReal.ofReal_coe_nnreal]

/-- The lower-tail event splits as a finite sum of binomial masses. -/
theorem retainedCount_tail_eq_sum
    (hmeas : ∀ r, Measurable (C r))
    (hindep : iIndepFun C μ)
    (hmarg : ∀ r, μ {ω | C r ω = true} = (q : ℝ≥0∞))
    (hq : q ≤ 1) (c : ℝ) :
    μ {ω | (retainedCountAt C ω : ℝ) ≤ c}
      = ∑ k ∈ (range (n + 1)).filter (fun k : ℕ => (k : ℝ) ≤ c),
          ENNReal.ofReal ((n.choose k : ℝ) * (q : ℝ) ^ k * (1 - (q : ℝ)) ^ (n - k)) := by
  have hset : {ω | (retainedCountAt C ω : ℝ) ≤ c}
      = ⋃ k ∈ (range (n + 1)).filter (fun k : ℕ => (k : ℝ) ≤ c),
          {ω | retainedCountAt C ω = k} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_filter,
      Finset.mem_range, exists_prop]
    constructor
    · intro h
      exact ⟨retainedCountAt C ω,
        ⟨Nat.lt_succ_of_le (retainedCount_le (fun r => C r ω)), h⟩, rfl⟩
    · rintro ⟨k, ⟨_, hk⟩, rfl⟩; exact hk
  rw [hset, measure_biUnion_finset]
  · exact Finset.sum_congr rfl
      (fun k _ => retainedCount_binomial_ofReal hmeas hindep hmarg hq k)
  · intro a _ b _ hab
    simp only [Function.onFun, Set.disjoint_left, Set.mem_setOf_eq]
    rintro ω ha hb
    exact hab (by rw [← ha, ← hb])
  · exact fun k _ => measurableSet_retainedCount_eq hmeas k

/-- **Chernoff lower-tail bound for the retained count.**
For `0 < η < 1`,
`μ {N ≤ (1-η) n q} ≤ exp (-(η² n q)/2)`. -/
theorem retainedCount_chernoff
    (hmeas : ∀ r, Measurable (C r))
    (hindep : iIndepFun C μ)
    (hmarg : ∀ r, μ {ω | C r ω = true} = (q : ℝ≥0∞))
    (hq : q ≤ 1) (η : ℝ) (hη0 : 0 < η) (hη1 : η < 1) :
    μ {ω | (retainedCountAt C ω : ℝ) ≤ (1 - η) * n * (q : ℝ)}
      ≤ ENNReal.ofReal (Real.exp (-(η ^ 2 * n * (q : ℝ)) / 2)) := by
  have hq0 : (0 : ℝ) ≤ (q : ℝ) := q.coe_nonneg
  have hq1 : (q : ℝ) ≤ 1 := by exact_mod_cast hq
  have hsub : (0 : ℝ) ≤ 1 - (q : ℝ) := by linarith
  rw [retainedCount_tail_eq_sum hmeas hindep hmarg hq ((1 - η) * n * (q : ℝ)),
      ← ENNReal.ofReal_sum_of_nonneg
        (fun k _ => mul_nonneg (mul_nonneg (by positivity) (pow_nonneg hq0 _))
          (pow_nonneg hsub _))]
  apply ENNReal.ofReal_le_ofReal
  exact binomial_lower_tail n (q : ℝ) η hq0 hq1 hη0 hη1

end Law

section UnionBound

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {n : ℕ} {ι : Type*} [Fintype ι]

/-- **Simultaneous finite-query union bound.**
For a finite prespecified family of test-wise queries, each with independent iid
row-retention indicators `C i` and joint retention probability `q i`, the
probability that *some* query is under-retained is controlled by the sum of the
individual Chernoff bounds. -/
theorem retainedCount_union_bound
    {C : ι → Fin n → Ω → Bool} {q : ι → ℝ≥0}
    (hmeas : ∀ i r, Measurable (C i r))
    (hindep : ∀ i, iIndepFun (C i) μ)
    (hmarg : ∀ i r, μ {ω | C i r ω = true} = (q i : ℝ≥0∞))
    (hq : ∀ i, q i ≤ 1) (η : ℝ) (hη0 : 0 < η) (hη1 : η < 1) :
    μ {ω | ∃ i, (retainedCountAt (C i) ω : ℝ) ≤ (1 - η) * n * (q i : ℝ)}
      ≤ ∑ i, ENNReal.ofReal (Real.exp (-(η ^ 2 * n * (q i : ℝ)) / 2)) := by
  have hset : {ω | ∃ i, (retainedCountAt (C i) ω : ℝ) ≤ (1 - η) * n * (q i : ℝ)}
      = ⋃ i ∈ (univ : Finset ι),
          {ω | (retainedCountAt (C i) ω : ℝ) ≤ (1 - η) * n * (q i : ℝ)} := by
    ext ω; simp
  rw [hset]
  refine le_trans (measure_biUnion_finset_le _ _) ?_
  apply Finset.sum_le_sum
  intro i _
  exact retainedCount_chernoff (hmeas i) (hindep i) (hmarg i) (hq i) η hη0 hη1

end UnionBound

#print axioms retainedCount_le
#print axioms retainedCount_binomial
#print axioms retainedCount_chernoff
#print axioms retainedCount_union_bound

end RecoveryFormal
