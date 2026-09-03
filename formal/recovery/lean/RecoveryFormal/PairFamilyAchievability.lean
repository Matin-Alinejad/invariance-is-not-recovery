import Mathlib
import RecoveryFormal.SparsePairDAG

/-!
# pair-family achievability — Exact-recovery sample rate on the independent-pair Gaussian family

This file formalises the **achievability (upper-bound) direction** of the exact-recovery
sample rate for the explicit independent-pair Gaussian family:

> With `n` iid samples per coordinate and a per-pair signal margin `b > 0` against
> sub-Gaussian noise with variance proxy `v`, the pairwise threshold estimator recovers
> *all* `m` bits with probability at least `1 - δ` as soon as
> `n ≥ 8 v log(m/δ) / b²`.

This is a sample rate of **logarithmic order in the number of bits** `m` (and in `1/δ`), as
claimed in the written statement.

## Model

* `m` independent pairs, one Boolean bit `θ k` per pair.
* For pair `k` and sample `i`, the observation is `obs θ b Z k i ω = signal + noise`,
  where the signal is `b` if `θ k = true` and `0` otherwise, and `Z k i` is the noise.
* **Noise assumption (explicit).** For every pair `k`, the samples `Z k ·` are independent
  (`hindep`) and each `Z k i` is sub-Gaussian with variance proxy `v` (`hsub`).  Genuine
  Gaussian noise `N(0, v)` satisfies this assumption; see `gaussian_hasSubgaussianMGF`.
  (Using the sub-Gaussian class only *generalises* the Gaussian family: it does not weaken
  the claim.)
* The estimator `estimator θ b Z n k` thresholds the empirical mean of pair `k` at `b/2`.

## Main results

* `gaussian_hasSubgaussianMGF` : the standard Gaussian `N(0,v)` is sub-Gaussian with
  parameter `v`, certifying that the model instantiates to the explicit Gaussian family.
* `perpair_error_bound` : the per-pair error probability is at most `exp(-n b² / (8 v))`.
* `exact_recovery_upper_bound` : the exact-recovery sample rate of logarithmic order.

The matching information-theoretic lower bound (a Fano / χ²-style converse giving
`n = Ω(log m / b²)`) is **not** formalised here; see the accompanying report.
-/

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal

namespace RecoveryFormal
namespace PairFamily

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
variable {m : ℕ}

/-- Mean signal of pair `k`: `b` if the bit is on, else `0`. -/
def signal (θ : Fin m → Bool) (b : ℝ) (k : Fin m) : ℝ := if θ k then b else 0

/-- Observation for pair `k`, sample `i`: signal plus noise. -/
def obs (θ : Fin m → Bool) (b : ℝ) (Z : Fin m → ℕ → Ω → ℝ) (k : Fin m) (i : ℕ) (ω : Ω) : ℝ :=
  signal θ b k + Z k i ω

/-- Empirical mean of pair `k` over the first `n` samples. -/
noncomputable def empMean (θ : Fin m → Bool) (b : ℝ) (Z : Fin m → ℕ → Ω → ℝ) (n : ℕ) (k : Fin m) (ω : Ω) : ℝ :=
  (∑ i ∈ Finset.range n, obs θ b Z k i ω) / n

/-- Threshold estimator: pair `k`'s bit is declared *on* iff its empirical mean is `≥ b/2`. -/
noncomputable def estimator (θ : Fin m → Bool) (b : ℝ) (Z : Fin m → ℕ → Ω → ℝ) (n : ℕ) (k : Fin m)
    (ω : Ω) : Bool :=
  decide (b / 2 ≤ empMean θ b Z n k ω)

/-- **Gaussian instance of the noise assumption.** The centred real Gaussian `N(0, v)`
(as the identity random variable on its own sample space) is sub-Gaussian with variance
proxy `v`.  This certifies that the sub-Gaussian model instantiates to the explicit
independent-pair Gaussian family. -/
lemma gaussian_hasSubgaussianMGF (v : ℝ≥0) :
    HasSubgaussianMGF id v (gaussianReal 0 v) where
  integrable_exp_mul t := by
    simpa using integrable_exp_mul_gaussianReal (μ := (0 : ℝ)) (v := v) t
  mgf_le t := by
    rw [mgf_id_gaussianReal]; simp

/-- **Per-pair error bound.** For any pair `k`, the probability that the threshold estimator
misclassifies its bit is at most `exp(-n b² / (8 v))`. -/
lemma perpair_error_bound {n : ℕ} (hn : 0 < n) (θ : Fin m → Bool)
    (b : ℝ) (hb : 0 < b) (v : ℝ≥0) (hv : 0 < v)
    (Z : Fin m → ℕ → Ω → ℝ) [IsProbabilityMeasure P]
    (hindep : ∀ k, iIndepFun (fun i => Z k i) P)
    (hsub : ∀ k i, HasSubgaussianMGF (Z k i) v P) (k : Fin m) :
    P.real {ω | estimator θ b Z n k ω ≠ θ k}
      ≤ Real.exp (-((n : ℝ) * b ^ 2) / (8 * (v : ℝ))) := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hε : (0:ℝ) ≤ (n:ℝ) * b / 2 := by positivity
  have hexp : Real.exp (-(((n:ℝ)*b/2)^2) / (2 * n * (v:ℝ)))
      = Real.exp (-((n:ℝ)*b^2)/(8*(v:ℝ))) := by
    congr 1
    have hnR' : (n:ℝ) ≠ 0 := ne_of_gt hnR
    have hvR' : (v:ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hv)
    field_simp; ring
  cases hθ : θ k with
  | false =>
    have hset : {ω | estimator θ b Z n k ω ≠ false}
        = {ω | (n:ℝ) * b / 2 ≤ ∑ i ∈ Finset.range n, Z k i ω} := by
      ext ω
      have hmean : empMean θ b Z n k ω = (∑ i ∈ Finset.range n, Z k i ω) / n := by
        simp only [empMean, obs, signal, hθ, Bool.false_eq_true, if_false, zero_add]
      simp only [Set.mem_setOf_eq, estimator, hmean, ne_eq, Bool.not_eq_false,
        decide_eq_true_eq, le_div_iff₀ hnR]
      constructor <;> intro h <;> nlinarith [h]
    rw [hset]
    refine (HasSubgaussianMGF.measure_sum_range_ge_le_of_iIndepFun (hindep k)
      (c := v) (n := n) (fun i _ => hsub k i) hε).trans ?_
    rw [hexp]
  | true =>
    have hindepN : iIndepFun (fun i => (fun ω => -(Z k i ω))) P := by
      have := (hindep k).comp (g := fun _ => fun x : ℝ => -x) (fun _ => measurable_neg)
      simpa using this
    have hsubN : ∀ i, HasSubgaussianMGF (fun ω => -(Z k i ω)) v P := by
      intro i; have := (hsub k i).neg; simpa [Pi.neg_def] using this
    have hset : {ω | estimator θ b Z n k ω ≠ true}
        ⊆ {ω | (n:ℝ) * b / 2 ≤ ∑ i ∈ Finset.range n, (fun ω => -(Z k i ω)) ω} := by
      intro ω hω
      have hmean : empMean θ b Z n k ω = b + (∑ i ∈ Finset.range n, Z k i ω) / n := by
        simp only [empMean, obs, signal, hθ, if_true, Finset.sum_add_distrib,
          Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        field_simp
      simp only [Set.mem_setOf_eq, estimator, hmean, ne_eq, Bool.not_eq_true,
        decide_eq_false_iff_not, not_le] at hω
      simp only [Set.mem_setOf_eq, Finset.sum_neg_distrib]
      have h2 : (∑ i ∈ Finset.range n, Z k i ω) / n < -b/2 := by linarith
      rw [div_lt_iff₀ hnR] at h2
      nlinarith [h2]
    refine (measureReal_mono hset (measure_ne_top P _)).trans ?_
    refine (HasSubgaussianMGF.measure_sum_range_ge_le_of_iIndepFun hindepN
      (c := v) (n := n) (fun i _ => hsubN i) hε).trans ?_
    rw [hexp]

/-- Real-analytic core of the union bound: the sample-rate hypothesis forces the total
error `m · exp(-n b² / (8 v))` below `δ`. -/
lemma rate_arith (m n : ℕ) (b : ℝ) (hb : 0 < b) (v : ℝ≥0) (hv : 0 < v)
    (δ : ℝ) (hδ : 0 < δ)
    (hrate : (8 * (v : ℝ) * Real.log ((m : ℝ) / δ)) / b ^ 2 ≤ (n : ℝ)) :
    (m : ℝ) * Real.exp (-((n : ℝ) * b ^ 2) / (8 * (v : ℝ))) ≤ δ := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm; simp; positivity
  have hmpos : (0:ℝ) < m := by exact_mod_cast hm
  have hvR : (0:ℝ) < (v:ℝ) := by exact_mod_cast hv
  have hb2 : (0:ℝ) < b^2 := by positivity
  have hrate' : 8 * (v:ℝ) * Real.log ((m:ℝ)/δ) ≤ (n:ℝ) * b^2 := by
    rw [div_le_iff₀ hb2] at hrate; linarith [hrate]
  have h1 : Real.log ((m:ℝ)/δ) ≤ (n:ℝ) * b^2 / (8 * (v:ℝ)) := by
    rw [le_div_iff₀ (by positivity)]; nlinarith [hrate']
  have h2 : Real.exp (-((n:ℝ)*b^2)/(8*(v:ℝ))) ≤ δ/m := by
    have hle : Real.exp (-((n:ℝ)*b^2)/(8*(v:ℝ))) ≤ Real.exp (-Real.log ((m:ℝ)/δ)) := by
      apply Real.exp_le_exp.2
      have he : -((n:ℝ)*b^2)/(8*(v:ℝ)) = -((n:ℝ)*b^2/(8*(v:ℝ))) := by ring
      rw [he]; linarith [h1]
    rw [Real.exp_neg, Real.exp_log (by positivity), inv_div] at hle
    exact hle
  calc (m:ℝ) * Real.exp (-((n:ℝ)*b^2)/(8*(v:ℝ))) ≤ (m:ℝ) * (δ/m) :=
        mul_le_mul_of_nonneg_left h2 (le_of_lt hmpos)
    _ = δ := by field_simp

/-- **Exact-recovery sample rate (achievability / upper bound).**

For the independent-pair family with signal margin `b > 0` and sub-Gaussian noise of variance
proxy `v`, once the number of samples satisfies `n ≥ 8 v log(m/δ) / b²`, the pairwise
threshold estimator recovers *all* `m` bits simultaneously with probability at least `1 - δ`.

This is the correct exact-recovery sample rate of **logarithmic order in the number of bits**
`m` claimed in the written statement. -/
theorem exact_recovery_upper_bound {n : ℕ} (hn : 0 < n) (θ : Fin m → Bool)
    (b : ℝ) (hb : 0 < b) (v : ℝ≥0) (hv : 0 < v)
    (Z : Fin m → ℕ → Ω → ℝ) [IsProbabilityMeasure P]
    (hindep : ∀ k, iIndepFun (fun i => Z k i) P)
    (hsub : ∀ k i, HasSubgaussianMGF (Z k i) v P)
    (δ : ℝ) (hδ : 0 < δ)
    (hrate : (8 * (v : ℝ) * Real.log ((m : ℝ) / δ)) / b ^ 2 ≤ (n : ℝ)) :
    1 - δ ≤ P.real {ω | ∀ k, estimator θ b Z n k ω = θ k} := by
  set S := {ω | ∀ k, estimator θ b Z n k ω = θ k} with hS
  set E := fun k => {ω | estimator θ b Z n k ω ≠ θ k} with hE
  have hsubset : Sᶜ ⊆ ⋃ k, E k := by
    intro ω hω
    simp only [hS, Set.mem_compl_iff, Set.mem_setOf_eq, not_forall] at hω
    obtain ⟨k, hk⟩ := hω
    exact Set.mem_iUnion.2 ⟨k, hk⟩
  have hcompl : P.real Sᶜ ≤ δ := by
    calc P.real Sᶜ ≤ P.real (⋃ k, E k) := measureReal_mono hsubset (measure_ne_top P _)
      _ ≤ ∑ k, P.real (E k) := measureReal_iUnion_fintype_le _
      _ ≤ ∑ _k : Fin m, Real.exp (-((n : ℝ) * b ^ 2) / (8 * (v : ℝ))) :=
          Finset.sum_le_sum (fun k _ => perpair_error_bound hn θ b hb v hv Z hindep hsub k)
      _ = (m : ℝ) * Real.exp (-((n : ℝ) * b ^ 2) / (8 * (v : ℝ))) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ ≤ δ := rate_arith m n b hb v hv δ hδ hrate
  have hone : (1:ℝ) ≤ P.real S + P.real Sᶜ := by
    have hle : P.real (Set.univ : Set Ω) ≤ P.real S + P.real Sᶜ := by
      have hu : (Set.univ : Set Ω) = S ∪ Sᶜ := by simp
      rw [hu]; exact measureReal_union_le _ _
    simpa using hle
  linarith [hcompl, hone]

end PairFamily
end RecoveryFormal
