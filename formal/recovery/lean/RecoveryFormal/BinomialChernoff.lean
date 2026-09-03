import Mathlib

/-!
# Chernoff lower-tail bound for the binomial distribution

This file develops the purely real-analytic content behind the multiplicative
Chernoff lower-tail bound for a `Binomial n q` random variable, stated directly
in terms of the binomial probability mass function

  `T(k) = (n.choose k) * q ^ k * (1 - q) ^ (n - k)`.

The main result `binomial_lower_tail` shows

  `∑_{k ≤ (1-η) n q} T(k) ≤ exp (-(η² n q)/2)`

for `0 < η < 1`, which is exactly the Chernoff lower-tail estimate.
-/

open Real Finset

namespace RecoveryFormal

/-- Key one-variable inequality behind the tightness of the Chernoff optimum:
for `0 < t ≤ 1` we have `t² ≤ 2 t log t + 1`.

Equivalently `2 t log t + 1 - t² ≥ 0`, proved by showing the left-hand side is an
antitone function of `t` on `(0,1]` that vanishes at `t = 1`. -/
lemma chernoff_key (t : ℝ) (ht0 : 0 < t) (ht1 : t ≤ 1) :
    t ^ 2 ≤ 2 * t * Real.log t + 1 := by
  set g : ℝ → ℝ := fun x => 2 * x * Real.log x + 1 - x ^ 2 with hg
  have hderiv : ∀ x ∈ Set.Ioo t 1, HasDerivAt g (2 * Real.log x + 2 - 2 * x) x := by
    intro x hx
    have hx0 : 0 < x := lt_trans ht0 hx.1
    have hxlog : HasDerivAt (fun y => y * Real.log y) (Real.log x + 1) x :=
      Real.hasDerivAt_mul_log hx0.ne'
    have h2 := hxlog.const_mul (2 : ℝ)
    have h3 : HasDerivAt (fun x => x ^ 2) (2 * x) x := by simpa using hasDerivAt_pow 2 x
    have hd := (h2.add_const (1 : ℝ)).sub h3
    convert hd using 1
    · ext y; simp [hg]; ring
    · ring
  have hpos : ∀ x ∈ Set.Icc t 1, 0 < x := fun x hx => lt_of_lt_of_le ht0 hx.1
  have hcont : ContinuousOn g (Set.Icc t 1) := by
    apply ContinuousOn.sub
    · apply ContinuousOn.add
      · apply ContinuousOn.mul (by fun_prop)
        exact Real.continuousOn_log.mono (fun x hx => (hpos x hx).ne')
      · fun_prop
    · fun_prop
  have hmono : AntitoneOn g (Set.Icc t 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc t 1) hcont
    · intro x hx; rw [interior_Icc] at hx
      exact (hderiv x hx).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      rw [(hderiv x hx).deriv]
      have hx0 : 0 < x := lt_trans ht0 hx.1
      have := Real.log_le_sub_one_of_pos hx0
      linarith
  have hg1 : g 1 = 0 := by simp [hg]
  have hle : g 1 ≤ g t := hmono (Set.left_mem_Icc.mpr ht1) (Set.right_mem_Icc.mpr ht1) ht1
  rw [hg1] at hle
  simp only [hg] at hle
  nlinarith [hle]

/-- Binomial theorem, arranged as the moment generating function identity:
`∑_{k=0}^n T(k) sᵏ = (1 - q + q s)ⁿ`. -/
lemma binomial_mgf_identity (n : ℕ) (q s : ℝ) :
    ∑ k ∈ range (n + 1),
        ((n.choose k : ℝ) * q ^ k * (1 - q) ^ (n - k)) * s ^ k
      = (1 - q + q * s) ^ n := by
  rw [show (1 - q + q * s) = q * s + (1 - q) by ring, add_pow]
  apply Finset.sum_congr rfl
  intro k _
  rw [mul_pow]; ring

/-- Elementary bound `(1 - q + q s)ⁿ ≤ exp (n q (s - 1))` valid whenever the base
is nonnegative (in particular for `0 ≤ q ≤ 1` and `0 ≤ s`). -/
lemma binomial_base_le_exp (n : ℕ) (q s : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hs0 : 0 ≤ s) :
    (1 - q + q * s) ^ n ≤ Real.exp ((n : ℝ) * q * (s - 1)) := by
  have hbase : (0 : ℝ) ≤ 1 - q + q * s := by nlinarith
  have h1 : 1 - q + q * s ≤ Real.exp (q * (s - 1)) := by
    have := Real.add_one_le_exp (q * (s - 1)); nlinarith [this]
  calc (1 - q + q * s) ^ n ≤ (Real.exp (q * (s - 1))) ^ n :=
        pow_le_pow_left₀ hbase h1 n
    _ = Real.exp ((n : ℝ) * q * (s - 1)) := by rw [← Real.exp_nat_mul]; ring_nf

/-- **Chernoff lower-tail bound for the binomial pmf.**
For `0 ≤ q ≤ 1` and `0 < η < 1`,
`∑_{k ≤ (1-η) n q} T(k) ≤ exp (-(η² n q)/2)`. -/
theorem binomial_lower_tail (n : ℕ) (q η : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hη0 : 0 < η) (hη1 : η < 1) :
    ∑ k ∈ (range (n + 1)).filter (fun k : ℕ => (k : ℝ) ≤ (1 - η) * n * q),
        (n.choose k : ℝ) * q ^ k * (1 - q) ^ (n - k)
      ≤ Real.exp (-(η ^ 2 * n * q) / 2) := by
  set s : ℝ := 1 - η with hs_def
  set a : ℝ := (1 - η) * n * q with ha_def
  have hs0 : 0 < s := by rw [hs_def]; linarith
  have hs1 : s < 1 := by rw [hs_def]; linarith
  have hsub : (0 : ℝ) ≤ 1 - q := by linarith
  set T : ℕ → ℝ := fun k => (n.choose k : ℝ) * q ^ k * (1 - q) ^ (n - k) with hT_def
  have hT : ∀ k, 0 ≤ T k := by
    intro k; rw [hT_def]
    exact mul_nonneg (mul_nonneg (by positivity) (pow_nonneg hq0 _)) (pow_nonneg hsub _)
  have key1 : ∑ k ∈ (range (n + 1)).filter (fun k : ℕ => (k : ℝ) ≤ a), T k
      ≤ ∑ k ∈ range (n + 1), T k * s ^ ((k : ℝ) - a) := by
    calc ∑ k ∈ (range (n + 1)).filter (fun k : ℕ => (k : ℝ) ≤ a), T k
        ≤ ∑ k ∈ (range (n + 1)).filter (fun k : ℕ => (k : ℝ) ≤ a),
            T k * s ^ ((k : ℝ) - a) := by
          apply Finset.sum_le_sum
          intro k hk
          have hka : (k : ℝ) ≤ a := (Finset.mem_filter.mp hk).2
          have h1 : (1 : ℝ) ≤ s ^ ((k : ℝ) - a) :=
            Real.one_le_rpow_of_pos_of_le_one_of_nonpos hs0 (le_of_lt hs1) (by linarith)
          nlinarith [hT k]
      _ ≤ ∑ k ∈ range (n + 1), T k * s ^ ((k : ℝ) - a) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          intro k _ _
          exact mul_nonneg (hT k) (le_of_lt (Real.rpow_pos_of_pos hs0 _))
  have key2 : ∑ k ∈ range (n + 1), T k * s ^ ((k : ℝ) - a)
      = s ^ (-a) * ∑ k ∈ range (n + 1), T k * s ^ k := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [show (k : ℝ) - a = -a + (k : ℝ) by ring, Real.rpow_add hs0, Real.rpow_natCast]
    ring
  have key3 : ∑ k ∈ range (n + 1), T k * s ^ k = (1 - q + q * s) ^ n :=
    binomial_mgf_identity n q s
  have hsa_pos : 0 < s ^ (-a) := Real.rpow_pos_of_pos hs0 _
  have main : ∑ k ∈ (range (n + 1)).filter (fun k : ℕ => (k : ℝ) ≤ a), T k
      ≤ s ^ (-a) * (1 - q + q * s) ^ n := by
    rw [← key3, ← key2]; exact key1
  have hbase := binomial_base_le_exp n q s hq0 hq1 (le_of_lt hs0)
  have step4 : s ^ (-a) * (1 - q + q * s) ^ n
      ≤ s ^ (-a) * Real.exp ((n : ℝ) * q * (s - 1)) :=
    mul_le_mul_of_nonneg_left hbase (le_of_lt hsa_pos)
  have hexp : s ^ (-a) = Real.exp (Real.log s * (-a)) := Real.rpow_def_of_pos hs0 (-a)
  have hexpo : Real.log s * (-a) + (n : ℝ) * q * (s - 1) ≤ -(η ^ 2 * n * q) / 2 := by
    have hkey := chernoff_key s hs0 (le_of_lt hs1)
    have hnq : 0 ≤ (n : ℝ) * q := by positivity
    rw [hs_def, ha_def] at *
    nlinarith [hkey, hnq, mul_nonneg hnq (sub_nonneg.mpr hkey)]
  calc ∑ k ∈ (range (n + 1)).filter (fun k : ℕ => (k : ℝ) ≤ a), T k
      ≤ s ^ (-a) * Real.exp ((n : ℝ) * q * (s - 1)) := le_trans main step4
    _ = Real.exp (Real.log s * (-a) + (n : ℝ) * q * (s - 1)) := by rw [hexp, ← Real.exp_add]
    _ ≤ Real.exp (-(η ^ 2 * n * q) / 2) := Real.exp_le_exp.mpr hexpo

end RecoveryFormal
