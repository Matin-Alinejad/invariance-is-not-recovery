import Mathlib

/-!
# conditional error aggregation — Conditional Type-I validity in the Gaussian-preserving regime

## Manuscript claim (verbatim)

> Conditional on retained sample size `m`, retained rows are iid Gaussian under the
> Gaussian-preserving selection theorem. Under the null, the partial-correlation `t`
> statistic has its Student-t law; conservative non-rejection for insufficient
> samples yields unconditional Type-I error at most `α`.

## What is (and is not) machine-verified here

The scientific pipeline behind the claim has three ingredients:

1. **Gaussian-preserving selection theorem.** Conditional on the retained sample
   size `m` (and the retained index set), the retained rows are iid Gaussian.
2. **Exact null law of the partial-correlation `t` statistic.** For a sufficient
   sample size (`m > |S| + 2`, so the degrees of freedom `df = m - |S| - 2 > 0`),
   under the null the sample partial-correlation `t` statistic follows a Student-t
   law with `df` degrees of freedom, whence the *conditional* rejection
   probability of a level-`α` test is at most `α`.
3. **Total-probability aggregation.** Combining the conditional Type-I control on
   the sufficient regime with *conservative non-rejection* on the insufficient
   regime (`m ≤ |S| + 2`, where the test never rejects), the *unconditional*
   Type-I error is at most `α`.

Ingredients (1) and (2) are deep distributional facts that are **not currently
available in Mathlib** (there is no multivariate-normal selection theorem and no
partial-correlation / Student-t null-law API of the required form). Per the task
policy we do **not** fabricate them. They enter the formalization *honestly, as
explicit hypotheses*:

* the Gaussian-preserving selection theorem and the Student-t null law together
  justify the hypothesis `h_suff` below (conditional Type-I control on the
  sufficient regime);
* the conservative construction of the test justifies `h_insuff` (never reject on
  the insufficient regime).

Ingredient (3) — the total-probability aggregation that turns conditional control
into unconditional control — is the genuinely non-trivial *probabilistic* content
that is proved here from first principles in Mathlib, with no proof holes, no
project-specific assumptions, and no `decide`-style shortcuts (see the recorded
list of axiom dependencies printed by `Main.lean`).

## Modelling dictionary

* `Ω`, `μ` : the probability space carrying all the randomness (data before
  selection). `μ` is a probability measure.
* `m : Ω → ℕ` : the retained sample size random variable (measurable).
* `reject : Set Ω` : the event that the conditional-independence test rejects the
  null hypothesis (a measurable event).
* `d0 : ℕ` : the depth/denominator offset `|S| + 2`; "insufficient samples" means
  `m ≤ d0`, "sufficient samples" means `m > d0` (so `df = m - d0 > 0`).
* `α : ℝ≥0∞` : the target significance level.

All positivity, measurability, support and denominator hypotheses of the stated result are
kept explicit: measurability of `m` and `reject`, that `μ` is a probability
measure, the depth split at `d0`, and the two conditional-probability bounds.
-/

namespace RecoveryFormal

open MeasureTheory ProbabilityTheory ENNReal

/-- **Core total-probability bound (product form).**

If, for every value `k` of the retained sample size `m`, the mass that the test
puts on rejecting *and* observing `m = k` is at most `α` times the mass of
`m = k`, then the unconditional rejection probability is at most `α`.

This is the measure-theoretic law-of-total-probability aggregation: it does not
depend on any distributional assumption, only on the fibered bounds. -/
theorem unconditional_le_of_conditional_product_bounds
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (m : Ω → ℕ) (hm : Measurable m) (reject : Set Ω) (hr : MeasurableSet reject)
    (α : ℝ≥0∞)
    (hbound : ∀ k, μ (reject ∩ (m ⁻¹' {k})) ≤ α * μ (m ⁻¹' {k})) :
    μ reject ≤ α := by
  have hcover : reject = ⋃ k, reject ∩ (m ⁻¹' {k}) := by ext ω; simp
  have huniv : (⋃ k, m ⁻¹' {k}) = (Set.univ : Set Ω) := by ext ω; simp
  have hdisj : Pairwise (Function.onFun Disjoint (fun k => reject ∩ (m ⁻¹' {k}))) := by
    intro i j hij
    exact Disjoint.mono Set.inter_subset_right Set.inter_subset_right
      (Disjoint.preimage m (by simp [hij]))
  have hmeas : ∀ k, MeasurableSet (reject ∩ (m ⁻¹' {k})) :=
    fun k => hr.inter (hm (measurableSet_singleton k))
  calc μ reject = μ (⋃ k, reject ∩ (m ⁻¹' {k})) := by rw [← hcover]
    _ = ∑' k, μ (reject ∩ (m ⁻¹' {k})) := measure_iUnion hdisj hmeas
    _ ≤ ∑' k, α * μ (m ⁻¹' {k}) := ENNReal.tsum_le_tsum hbound
    _ = α * ∑' k, μ (m ⁻¹' {k}) := ENNReal.tsum_mul_left
    _ = α * μ (⋃ k, m ⁻¹' {k}) := by
            rw [measure_iUnion (fun i j hij => Disjoint.preimage m (by simp [hij]))
              (fun k => hm (measurableSet_singleton k))]
    _ = α := by rw [huniv]; simp

/-- A conditional (Bayes) bound `μ[reject | s] ≤ α` implies the product-form bound
`μ(reject ∩ s) ≤ α · μ(s)`, for any measurable `s` under a finite measure. The
degenerate case `μ s = 0` is handled automatically. -/
theorem product_bound_of_cond_le
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (s reject : Set Ω) (hs : MeasurableSet s) (α : ℝ≥0∞)
    (h : (μ[|s]) reject ≤ α) : μ (reject ∩ s) ≤ α * μ s := by
  rw [ProbabilityTheory.cond_apply hs] at h
  rcases eq_or_ne (μ s) 0 with h0 | h0
  · calc μ (reject ∩ s) ≤ μ s := measure_mono Set.inter_subset_right
      _ = 0 := h0
      _ ≤ α * μ s := zero_le _
  · have hfin : μ s ≠ ∞ := measure_ne_top μ s
    have hmul : μ s * ((μ s)⁻¹ * μ (s ∩ reject)) ≤ μ s * α := by gcongr
    rw [← mul_assoc, ENNReal.mul_inv_cancel h0 hfin, one_mul, Set.inter_comm,
      mul_comm] at hmul
    exact hmul

/-- **conditional error aggregation — Unconditional Type-I error control (conditional / Bayes form).**

Fix the depth offset `d0 = |S| + 2`, so a sample is *insufficient* when the
retained size satisfies `m ≤ d0` and *sufficient* when `m > d0`.

Hypotheses:

* `h_insuff` — *conservative non-rejection on the insufficient regime.* For every
  insufficient size `k ≤ d0`, the test never rejects while `m = k`
  (`μ(reject ∩ {m = k}) = 0`). This is a property of the (conservatively
  constructed) test and requires **no** distributional input.

* `h_suff` — *conditional Type-I control on the sufficient regime.* For every
  sufficient size `k > d0`, the conditional rejection probability
  `μ[reject | {m = k}]` is at most `α`. This is exactly where the
  Gaussian-preserving selection theorem (iid Gaussian retained rows) and the
  Student-t null law of the partial-correlation `t` statistic (with
  `df = k - d0 > 0`) are used; they are supplied here as an explicit hypothesis
  because those distributional theorems are not available in Mathlib.

Conclusion: the *unconditional* Type-I error `μ(reject)` is at most `α`. -/
theorem type_I_error_le_alpha
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (m : Ω → ℕ) (hm : Measurable m) (reject : Set Ω) (hr : MeasurableSet reject)
    (d0 : ℕ) (α : ℝ≥0∞)
    (h_insuff : ∀ k, k ≤ d0 → μ (reject ∩ (m ⁻¹' {k})) = 0)
    (h_suff : ∀ k, d0 < k → (μ[|(m ⁻¹' {k})]) reject ≤ α) :
    μ reject ≤ α := by
  apply unconditional_le_of_conditional_product_bounds μ m hm reject hr α
  intro k
  rcases le_or_gt k d0 with hk | hk
  · rw [h_insuff k hk]; exact zero_le _
  · have hmeask : MeasurableSet (m ⁻¹' {k}) := hm (measurableSet_singleton k)
    exact product_bound_of_cond_le μ (m ⁻¹' {k}) reject hmeask α (h_suff k hk)

end RecoveryFormal
