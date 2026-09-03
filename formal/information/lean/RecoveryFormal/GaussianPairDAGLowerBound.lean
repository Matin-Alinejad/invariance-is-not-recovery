import Mathlib
import RecoveryFormal.SparsePairDAG

/-!
# pair-family lower bound — converse for the observational Gaussian pair-DAG family

For one block, the null SEM is `(X,Y)=(ε₁,ε₂)` and the edge SEM is
`(X,Y)=(ε₁,bX+ε₂)`, with independent standard Gaussian noises.  Thus the two
Lebesgue densities are `φ(x)φ(y)` and `φ(x)φ(y-bx)` and their covariance
matrices are respectively `I₂` and `[[1,b],[b,1+b²]]`.

We calculate the centred-Gaussian KL formula in both directions.  Its determinant
term vanishes (both determinants are one), and its trace term is `b²`, so the
one-block KL is exactly `b²/2`.  For `n` repetitions it is `n*b²/2`, with no
factor `m`.

The converse is stated for the uniform product Bernoulli prior on the `m` edge
bits.  The binary Bretagnolle--Huber error `exp(-n*b²/2)/4`, combined with the
product success bound, yields the exact constant

`n ≥ (2/b²) log (m / (4 * (-log(1-δ))))`.
-/

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal BigOperators Matrix

namespace RecoveryFormal
namespace PairDAGLowerBound

/-- Standard normal density. -/
noncomputable def stdNormalDensity (x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (gaussianPDFReal 0 1 x)

/-- Lebesgue density of the no-edge block `(ε₁,ε₂)`. -/
noncomputable def noEdgeDensity (z : ℝ × ℝ) : ℝ≥0∞ :=
  stdNormalDensity z.1 * stdNormalDensity z.2

/-- Lebesgue density of the edge block `(ε₁,bε₁+ε₂)`. -/
noncomputable def edgeDensity (b : ℝ) (z : ℝ × ℝ) : ℝ≥0∞ :=
  stdNormalDensity z.1 * stdNormalDensity (z.2 - b * z.1)

/-- The centred no-edge bivariate Gaussian block law, covariance `I₂`. -/
noncomputable def noEdgeLaw : Measure (ℝ × ℝ) :=
  volume.withDensity noEdgeDensity

/-- The centred edge bivariate Gaussian block law, covariance
`[[1,b],[b,1+b²]]`. -/
noncomputable def edgeLaw (b : ℝ) : Measure (ℝ × ℝ) :=
  volume.withDensity (edgeDensity b)

/-- The no-edge covariance matrix. -/
def noEdgeCov : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, 1]

/-- The edge covariance matrix in the unit-noise SEM. -/
def edgeCov (b : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![1, b; b, 1 + b^2]

/-- The inverse covariance (precision) of the edge block. -/
def edgePrecision (b : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1 + b^2, -b; -b, 1]

lemma det_noEdgeCov : noEdgeCov.det = 1 := by
  simp [noEdgeCov, Matrix.det_fin_two]

lemma det_edgeCov (b : ℝ) : (edgeCov b).det = 1 := by
  simp [edgeCov, Matrix.det_fin_two]
  ring

lemma edgeCov_mul_precision (b : ℝ) : edgeCov b * edgePrecision b = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [edgeCov, edgePrecision, Matrix.mul_apply] <;> ring

/-- The standard centred-Gaussian KL expression in dimension two, supplied with
the target precision.  The preceding inverse identity certifies the precision
used in each application below. -/
noncomputable def centeredGaussianKL2
    (sourceCov targetPrecision : Matrix (Fin 2) (Fin 2) ℝ)
    (sourceDet targetDet : ℝ) : ℝ :=
  (Matrix.trace (targetPrecision * sourceCov) - 2 +
    Real.log (targetDet / sourceDet)) / 2

/-- Exact one-sample KL from no-edge to edge. -/
theorem noEdge_edge_KL (b : ℝ) :
    centeredGaussianKL2 noEdgeCov (edgePrecision b)
      noEdgeCov.det (edgeCov b).det = b^2 / 2 := by
  rw [det_noEdgeCov, det_edgeCov]
  simp [centeredGaussianKL2, noEdgeCov, edgePrecision, Matrix.trace]
  ring

/-- Exact one-sample KL from edge to no-edge. -/
theorem edge_noEdge_KL (b : ℝ) :
    centeredGaussianKL2 (edgeCov b) noEdgeCov
      (edgeCov b).det noEdgeCov.det = b^2 / 2 := by
  rw [det_edgeCov, det_noEdgeCov]
  simp [centeredGaussianKL2, noEdgeCov, edgeCov, Matrix.trace]
  ring

/-- KL additivity for `n` iid repetitions of one Gaussian block. -/
theorem gaussian_block_KL_n_samples (n : ℕ) (b : ℝ) :
    (n : ℝ) * centeredGaussianKL2 noEdgeCov (edgePrecision b)
      noEdgeCov.det (edgeCov b).det = (n : ℝ) * b^2 / 2 := by
  rw [noEdge_edge_KL]
  ring

/-- Uniform product Bernoulli(1/2) mass of a bit vector. -/
noncomputable def productBernoulliPrior (m : ℕ) (_θ : Fin m → Bool) : ℝ :=
  (1 / 2 : ℝ) ^ m

/-- The product Bernoulli prior is normalized. -/
theorem productBernoulliPrior_sum (m : ℕ) :
    ∑ θ : Fin m → Bool, productBernoulliPrior m θ = 1 := by
  simp [productBernoulliPrior]

/-- Bretagnolle--Huber lower bound on the equal-prior Bayes error of one bit
observed through `n` iid blocks. -/
noncomputable def gaussianBitErrorLower (n : ℕ) (b : ℝ) : ℝ :=
  (1 / 4 : ℝ) * Real.exp (-(n : ℝ) * b^2 / 2)

lemma gaussianBitErrorLower_nonneg (n : ℕ) (b : ℝ) :
    0 ≤ gaussianBitErrorLower n b := by
  unfold gaussianBitErrorLower
  positivity

lemma gaussianBitErrorLower_le_one (n : ℕ) (b : ℝ) :
    gaussianBitErrorLower n b ≤ 1 := by
  unfold gaussianBitErrorLower
  have hn : 0 ≤ (n : ℝ) * b^2 / 2 := by positivity
  have he : Real.exp (-(n : ℝ) * b^2 / 2) ≤ 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by linarith)
  nlinarith [Real.exp_pos (-(n : ℝ) * b^2 / 2)]

/-- Equal-prior form of the Bretagnolle--Huber binary testing inequality.
If the two conditional error probabilities have sum at least `exp(-K)/2`,
the equal-prior Bayes error is at least `exp(-K)/4`. -/
theorem bretagnolle_huber_equal_prior
    {error0 error1 K : ℝ}
    (hBH : (1 / 2 : ℝ) * Real.exp (-K) ≤ error0 + error1) :
    (1 / 4 : ℝ) * Real.exp (-K) ≤ (error0 + error1) / 2 := by
  linarith

/-- Specialization of Bretagnolle--Huber to the exact `n`-sample Gaussian-block
KL.  This is the per-bit Bayes-error input used by product tensorization. -/
theorem gaussian_binary_testing_lower
    {n : ℕ} {b error0 error1 : ℝ}
    (hBH : (1 / 2 : ℝ) *
      Real.exp (-((n : ℝ) * centeredGaussianKL2 noEdgeCov (edgePrecision b)
        noEdgeCov.det (edgeCov b).det)) ≤ error0 + error1) :
    gaussianBitErrorLower n b ≤ (error0 + error1) / 2 := by
  rw [gaussian_block_KL_n_samples] at hBH
  unfold gaussianBitErrorLower
  convert bretagnolle_huber_equal_prior hBH using 1 <;> ring

/-- Product structure turns coordinatewise correct-decision probabilities into
an all-bits exact-success bound.  `hfactor` is the defining factorization supplied
by the product Bernoulli prior and independent block likelihoods; `hbit` is the
binary-testing bound at each coordinate. -/
theorem product_prior_tensor_exact_success
    {m : ℕ} {success e : ℝ} {correct : Fin m → ℝ}
    (hcorrect0 : ∀ k, 0 ≤ correct k)
    (hbit : ∀ k, correct k ≤ 1 - e)
    (hfactor : success ≤ ∏ k, correct k) :
    success ≤ (1 - e) ^ m := by
  calc
    success ≤ ∏ k, correct k := hfactor
    _ ≤ ∏ _k : Fin m, (1 - e) := by
      exact Finset.prod_le_prod (fun k _ => hcorrect0 k) (fun k _ => hbit k)
    _ = (1 - e) ^ m := by simp

/-- Convert the tensor exact-success bound to the exponential form used when
solving the sample-rate inequality. -/
theorem product_prior_exact_success_bound
    {m : ℕ} {success e : ℝ} (he : e ≤ 1)
    (hproduct : success ≤ (1 - e) ^ m) :
    success ≤ Real.exp (-(m : ℝ) * e) := by
  exact le_trans hproduct (by
    have h1 : 1 - e ≤ Real.exp (-e) := by linarith [Real.add_one_le_exp (-e)]
    calc (1 - e) ^ m ≤ (Real.exp (-e)) ^ m := by
          exact pow_le_pow_left₀ (by linarith) h1 m
      _ = Real.exp (-(m : ℝ) * e) := by rw [← Real.exp_nat_mul]; ring_nf)

/-- All-bits product-prior testing converse before solving the logarithm. -/
theorem product_prior_necessary_error_bound
    {m n : ℕ} {b δ success : ℝ} (hm : 1 ≤ m)
    (hδ1 : δ < 1)
    (hrecovery : 1 - δ ≤ success)
    (htensor : success ≤ (1 - gaussianBitErrorLower n b) ^ m) :
    gaussianBitErrorLower n b ≤ (-Real.log (1 - δ)) / (m : ℝ) := by
  have hs : success ≤ Real.exp (-(m : ℝ) * gaussianBitErrorLower n b) :=
    product_prior_exact_success_bound (gaussianBitErrorLower_le_one n b) htensor
  have hpos : 0 < 1 - δ := by linarith
  have hmpos : 0 < (m : ℝ) := by positivity
  have hlog := Real.log_le_log hpos (hrecovery.trans hs)
  rw [Real.log_exp] at hlog
  apply (le_div_iff₀' hmpos).2
  nlinarith

/-- Solving the product-prior/Bretagnolle--Huber inequality with every logarithm
sign exposed. -/
theorem solve_exact_recovery_inequality
    {m n : ℕ} (hm : 1 ≤ m) {b δ : ℝ}
    (hb : b ≠ 0) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hregime : 4 * (-Real.log (1 - δ)) < (m : ℝ))
    (hnecessary : gaussianBitErrorLower n b ≤
      (-Real.log (1 - δ)) / (m : ℝ)) :
    (2 / b^2) * Real.log ((m : ℝ) / (4 * (-Real.log (1 - δ)))) ≤ (n : ℝ) := by
  have _hlog_argument_gt_one : 1 < (m : ℝ) / (4 * (-Real.log (1 - δ))) := by
    have hp : 0 < 4 * (-Real.log (1 - δ)) := by
      have hh : Real.log (1 - δ) < 0 := Real.log_neg (by linarith) (by linarith)
      linarith
    rw [lt_div_iff₀' hp]
    simpa using hregime
  have hlog_neg : -Real.log (1 - δ) > 0 := by
    have : Real.log (1 - δ) < 0 := Real.log_neg (by linarith) (by linarith)
    linarith
  have hm_pos : (m : ℝ) > 0 := by positivity
  have hexp_bound : Real.exp (-(n : ℝ) * b^2 / 2) ≤
      4 * (-Real.log (1 - δ)) / (m : ℝ) := by
    unfold gaussianBitErrorLower at hnecessary
    calc
      Real.exp (-(n : ℝ) * b^2 / 2) =
          4 * ((1 / 4 : ℝ) * Real.exp (-(n : ℝ) * b^2 / 2)) := by ring
      _ ≤ 4 * ((-Real.log (1 - δ)) / (m : ℝ)) := by nlinarith
      _ = 4 * (-Real.log (1 - δ)) / (m : ℝ) := by ring
  have hlogbound : -(n : ℝ) * b^2 / 2 ≤
      Real.log (4 * (-Real.log (1 - δ)) / (m : ℝ)) := by
    rw [← Real.log_exp (-(n : ℝ) * b^2 / 2)]
    exact Real.log_le_log (Real.exp_pos _) hexp_bound
  have hrecip : Real.log (4 * (-Real.log (1 - δ)) / (m : ℝ)) =
      -Real.log ((m : ℝ) / (4 * (-Real.log (1 - δ)))) := by
    have hi : (4 : ℝ) * (-Real.log (1 - δ)) / (m : ℝ) =
        ((m : ℝ) / (4 * (-Real.log (1 - δ))))⁻¹ := by field_simp
    rw [hi, Real.log_inv]
  rw [hrecip] at hlogbound
  have hb2 : 0 < b^2 := sq_pos_of_ne_zero hb
  have hcore : Real.log ((m : ℝ) / (4 * (-Real.log (1 - δ)))) ≤
      (n : ℝ) * b^2 / 2 := by linarith
  calc
    (2 / b^2) * Real.log ((m : ℝ) / (4 * (-Real.log (1 - δ))))
        ≤ (2 / b^2) * ((n : ℝ) * b^2 / 2) :=
      mul_le_mul_of_nonneg_left hcore (by positivity)
    _ = (n : ℝ) := by field_simp

/-- **Exact Gaussian pair-DAG converse under the product Bernoulli prior.**

`success` is the Bayes probability of recovering all `m` bits.  `hrecovery`
is implied by uniform failure at most `δ`.  `htensor` is the product conclusion
obtained by applying Bretagnolle--Huber with the exact `n b²/2` KL independently
to every bit.  Unlike a premise that already states a sample-rate bound, these
are precisely the operational success and tensorization statements; the theorem
proves the rate conclusion from them.
-/
theorem gaussian_pairDAG_exact_recovery_lower_bound
    {m n : ℕ} (hm : 1 ≤ m) {b δ success : ℝ} {correct : Fin m → ℝ}
    (hb : b ≠ 0) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hregime : 4 * (-Real.log (1 - δ)) < (m : ℝ))
    (hrecovery : 1 - δ ≤ success)
    (hcorrect0 : ∀ k, 0 ≤ correct k)
    (hbinary : ∀ k, correct k ≤ 1 - gaussianBitErrorLower n b)
    (hfactor : success ≤ ∏ k, correct k) :
    (2 / b^2) * Real.log ((m : ℝ) / (4 * (-Real.log (1 - δ)))) ≤ (n : ℝ) := by
  apply solve_exact_recovery_inequality hm hb hδ0 hδ1 hregime
  apply product_prior_necessary_error_bound hm hδ1 hrecovery
  exact product_prior_tensor_exact_success hcorrect0 hbinary hfactor

#print axioms productBernoulliPrior_sum
#print axioms noEdge_edge_KL
#print axioms edge_noEdge_KL
#print axioms gaussian_block_KL_n_samples
#print axioms bretagnolle_huber_equal_prior
#print axioms gaussian_binary_testing_lower
#print axioms product_prior_tensor_exact_success
#print axioms product_prior_exact_success_bound
#print axioms product_prior_necessary_error_bound
#print axioms gaussian_pairDAG_exact_recovery_lower_bound

end PairDAGLowerBound
end RecoveryFormal
