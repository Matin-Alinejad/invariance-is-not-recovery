import Mathlib

open Real

namespace RecoveryFormal

/-- Logistic observation probability. -/
noncomputable def logisticWeight (a b x : ℝ) : ℝ :=
  1 / (1 + Real.exp (-(a + b * x)))

/-- Log of an unnormalised selected Gaussian density, up to an additive constant. -/
noncomputable def selectedGaussianLogKernel
    (μ σ a b x : ℝ) : ℝ :=
  -((x - μ)^2) / (2 * σ^2) + Real.log (logisticWeight a b x)

/-!
Formal target:

Under σ ≠ 0 and b ≠ 0, prove that the second derivative of
`selectedGaussianLogKernel μ σ a b` is not constant. Conclude that no constants
μ' and σ' ≠ 0 make it equal everywhere, up to an additive constant, to
`-((x-μ')^2)/(2*σ'^2)`.

The intended derivative is
  -1/σ^2 - b^2 q(x)(1-q(x)),
where q is the logistic weight.
-/

/-- The logistic denominator `1 + exp(-(a+b x))` is strictly positive. -/
lemma one_add_exp_pos (a b x : ℝ) : 0 < 1 + Real.exp (-(a + b * x)) := by
  positivity

/-- The logistic weight is strictly positive. -/
lemma logisticWeight_pos (a b x : ℝ) : 0 < logisticWeight a b x := by
  unfold logisticWeight
  positivity

/-- The logistic weight is never zero. -/
lemma logisticWeight_ne_zero (a b x : ℝ) : logisticWeight a b x ≠ 0 :=
  ne_of_gt (logisticWeight_pos a b x)

/-- Complement identity: `1 - q(x) = exp(-(a+bx)) / (1 + exp(-(a+bx)))`. -/
lemma one_sub_logisticWeight (a b x : ℝ) :
    1 - logisticWeight a b x
      = Real.exp (-(a + b * x)) / (1 + Real.exp (-(a + b * x))) := by
  unfold logisticWeight
  have h := one_add_exp_pos a b x
  field_simp
  ring

/-- Derivative of the logistic weight: `q' = b · q · (1 - q)`. -/
lemma hasDerivAt_logisticWeight (a b x : ℝ) :
    HasDerivAt (logisticWeight a b)
      (b * logisticWeight a b x * (1 - logisticWeight a b x)) x := by
  have hden : (0:ℝ) < 1 + Real.exp (-(a + b * x)) := one_add_exp_pos a b x
  have hbase : HasDerivAt (fun x : ℝ => a + b * x) b x := by
    simpa using ((hasDerivAt_id x).const_mul b).const_add a
  have haff : HasDerivAt (fun x : ℝ => -(a + b * x)) (-b) x := hbase.neg
  have hexp : HasDerivAt (fun x : ℝ => Real.exp (-(a + b * x)))
      (Real.exp (-(a + b * x)) * (-b)) x := (Real.hasDerivAt_exp _).comp x haff
  have hden' : HasDerivAt (fun x : ℝ => 1 + Real.exp (-(a + b * x)))
      (Real.exp (-(a + b * x)) * (-b)) x := by
    simpa using hexp.const_add 1
  have hinv := hden'.inv (by positivity)
  have heq : logisticWeight a b = fun x => (1 + Real.exp (-(a + b * x)))⁻¹ := by
    funext y; unfold logisticWeight; rw [one_div]
  rw [heq]
  convert hinv using 1
  have hne : (1 + Real.exp (-(a + b * x))) ≠ 0 := ne_of_gt hden
  field_simp
  ring

/-- Derivative of the log of the logistic weight: `(log q)' = b (1 - q)`. -/
lemma hasDerivAt_logLogistic (a b x : ℝ) :
    HasDerivAt (fun x => Real.log (logisticWeight a b x))
      (b * (1 - logisticWeight a b x)) x := by
  have hq := hasDerivAt_logisticWeight a b x
  have hne : logisticWeight a b x ≠ 0 := logisticWeight_ne_zero a b x
  have := hq.log hne
  convert this using 1
  field_simp

/-- Derivative of the Gaussian log-term `-(x-μ)²/(2σ²)`. -/
lemma hasDerivAt_gaussTerm (μ σ x : ℝ) :
    HasDerivAt (fun y => -((y - μ)^2) / (2 * σ^2)) (-(x - μ) / σ^2) x := by
  have h : HasDerivAt (fun y : ℝ => -((y - μ)^2) / (2 * σ^2))
      (-(2*(x-μ)*(1-0)) / (2*σ^2)) x := by
    apply HasDerivAt.div_const
    apply HasDerivAt.neg
    have := ((hasDerivAt_id x).sub_const μ).pow 2
    simpa using this
  convert h using 1
  by_cases hσ : σ = 0
  · simp [hσ]
  · field_simp; ring

/-- Derivative of `-(x-μ)/σ²` is the constant `-1/σ²`. -/
lemma hasDerivAt_gaussTerm_deriv (μ σ x : ℝ) :
    HasDerivAt (fun y => -(y - μ) / σ^2) (-1 / σ^2) x := by
  apply HasDerivAt.div_const
  have := ((hasDerivAt_id x).sub_const μ).neg
  convert this using 1

/-- First derivative of the selected log-kernel. -/
lemma hasDerivAt_kernel (μ σ a b x : ℝ) :
    HasDerivAt (selectedGaussianLogKernel μ σ a b)
      (-(x - μ) / σ^2 + b * (1 - logisticWeight a b x)) x := by
  have h1 := hasDerivAt_gaussTerm μ σ x
  have h2 := hasDerivAt_logLogistic a b x
  exact h1.add h2

/-- The first derivative of the kernel, as a function. -/
lemma deriv_kernel (μ σ a b : ℝ) :
    deriv (selectedGaussianLogKernel μ σ a b)
      = fun x => -(x - μ) / σ^2 + b * (1 - logisticWeight a b x) := by
  funext x
  exact (hasDerivAt_kernel μ σ a b x).deriv

/-- Derivative of the first-derivative function of the kernel. -/
lemma hasDerivAt_D1 (μ σ a b x : ℝ) :
    HasDerivAt (fun x => -(x - μ) / σ^2 + b * (1 - logisticWeight a b x))
      (-1 / σ^2 - b^2 * logisticWeight a b x * (1 - logisticWeight a b x)) x := by
  have h1 : HasDerivAt (fun y => -(y - μ) / σ^2) (-1 / σ^2) x := by
    apply HasDerivAt.div_const
    have := ((hasDerivAt_id x).sub_const μ).neg
    convert this using 1
  have hq := hasDerivAt_logisticWeight a b x
  have h2 : HasDerivAt (fun x => b * (1 - logisticWeight a b x))
      (b * (-(b * logisticWeight a b x * (1 - logisticWeight a b x)))) x :=
    (hq.const_sub 1).const_mul b
  have := h1.add h2
  convert this using 1
  ring

/-- **Second-derivative formula** for the selected log-kernel:
`(log-kernel)'' (x) = -1/σ² - b² q(x)(1-q(x))`.

The hypothesis `σ ≠ 0` is a denominator condition of the model; it is kept to
match the written statement even though the second-derivative identity holds for all
`σ` (with Lean's `x / 0 = 0` convention). -/
theorem selectedGaussianLogKernel_secondDeriv (μ σ a b : ℝ) (hσ : σ ≠ 0) (x : ℝ) :
    deriv (deriv (selectedGaussianLogKernel μ σ a b)) x
      = -1 / σ^2 - b^2 * logisticWeight a b x * (1 - logisticWeight a b x) := by
  rw [deriv_kernel]
  exact (hasDerivAt_D1 μ σ a b x).deriv

/-- Second derivative of a Gaussian log-density `-(x-μ')²/(2σ'²) + c` is the
constant `-1/σ'²`. -/
lemma gaussConst_secondDeriv (μ' σ' c x : ℝ) :
    deriv (deriv (fun y => -((y - μ')^2) / (2 * σ'^2) + c)) x = -1 / σ'^2 := by
  have hd : deriv (fun y => -((y - μ')^2) / (2 * σ'^2) + c)
      = fun y => -(y - μ') / σ'^2 := by
    funext y
    exact ((hasDerivAt_gaussTerm μ' σ' y).add_const c).deriv
  rw [hd]
  exact (hasDerivAt_gaussTerm_deriv μ' σ' x).deriv

/-- At `x = -a/b` the logistic weight equals `1/2` (requires `b ≠ 0`). -/
lemma logisticWeight_at_half (a b : ℝ) (hb : b ≠ 0) :
    logisticWeight a b (-a / b) = 1 / 2 := by
  unfold logisticWeight
  have : -(a + b * (-a / b)) = 0 := by field_simp; ring
  rw [this, Real.exp_zero]
  norm_num

/-- At `x = (1-a)/b` the logistic weight is not `1/2` (requires `b ≠ 0`). -/
lemma logisticWeight_at_one_ne_half (a b : ℝ) (hb : b ≠ 0) :
    logisticWeight a b ((1 - a) / b) ≠ 1 / 2 := by
  unfold logisticWeight
  have hval : -(a + b * ((1 - a) / b)) = -1 := by field_simp; ring
  rw [hval]
  have hden : (0:ℝ) < 1 + Real.exp (-1) := by positivity
  intro h
  rw [div_eq_iff (ne_of_gt hden)] at h
  have hexp1 : Real.exp (-1 : ℝ) = 1 := by linarith
  have h0 : (-1 : ℝ) = 0 := by rw [← Real.exp_eq_one_iff]; exact hexp1
  norm_num at h0

/-- **Nonconstant second derivative.** Under `σ ≠ 0` and `b ≠ 0`, the second
derivative of the selected log-kernel takes different values at two points, hence
is not constant. -/
theorem secondDeriv_nonconstant (μ σ a b : ℝ) (hσ : σ ≠ 0) (hb : b ≠ 0) :
    ∃ x₁ x₂, deriv (deriv (selectedGaussianLogKernel μ σ a b)) x₁
           ≠ deriv (deriv (selectedGaussianLogKernel μ σ a b)) x₂ := by
  refine ⟨-a / b, (1 - a) / b, ?_⟩
  rw [selectedGaussianLogKernel_secondDeriv μ σ a b hσ,
      selectedGaussianLogKernel_secondDeriv μ σ a b hσ,
      logisticWeight_at_half a b hb]
  set q := logisticWeight a b ((1 - a) / b) with hqdef
  have hq : q ≠ 1 / 2 := logisticWeight_at_one_ne_half a b hb
  have hb2 : (0:ℝ) < b^2 := by positivity
  intro heq
  have key : b^2 * (q - 1/2)^2 = 0 := by nlinarith [heq]
  rcases mul_eq_zero.1 key with h | h
  · linarith
  · apply hq; nlinarith [h]

/-- **Non-Gaussian conclusion.** Under `σ ≠ 0` and `b ≠ 0`, there are no
constants `μ'`, `σ' ≠ 0`, `c` making the selected log-kernel equal everywhere to
a Gaussian log-density `-(x-μ')²/(2σ'²) + c`.  A Gaussian log-density has constant
second derivative, whereas the selected log-kernel does not. -/
theorem selected_not_gaussian (μ σ a b : ℝ) (hσ : σ ≠ 0) (hb : b ≠ 0) :
    ¬ ∃ (μ' σ' c : ℝ), σ' ≠ 0 ∧
        ∀ x, selectedGaussianLogKernel μ σ a b x
             = -((x - μ')^2) / (2 * σ'^2) + c := by
  rintro ⟨μ', σ', c, hσ', heq⟩
  have hfun : selectedGaussianLogKernel μ σ a b
      = fun y => -((y - μ')^2) / (2 * σ'^2) + c := funext heq
  obtain ⟨x₁, x₂, hne⟩ := secondDeriv_nonconstant μ σ a b hσ hb
  apply hne
  rw [hfun, gaussConst_secondDeriv, gaussConst_secondDeriv]

end RecoveryFormal
