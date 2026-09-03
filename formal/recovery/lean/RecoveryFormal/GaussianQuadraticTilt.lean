import Mathlib

open Matrix MeasureTheory

namespace RecoveryFormal

/-!
# Gaussian quadratic tilt — Gaussian-preserving exponential-quadratic self-masking

## Scientific claim

Multiplying a multivariate Gaussian density by a positive coordinate-separable
exponential-quadratic selection weight yields another Gaussian with precision
`Σ⁻¹ + A` and mean `(Σ⁻¹ + A)⁻¹ (Σ⁻¹ μ + b)`.

Here the Gaussian is written in **precision form**: `Q := Σ⁻¹` is the precision
(inverse covariance).  The selection weight is
`w(x) = exp(-½ xᵀ A x + bᵀ x)`, which is positive for every `x` and separable
across coordinates when `A` and `b` are diagonal / coordinatewise.

This file proves:

* `scalar_gaussian_tilt_completion` — the scalar completion-of-the-square
  (milestone 1).
* `dp_symm`, `qform_add_split`, `qform_sub_symm` — bilinear-form helper lemmas.
* `matrix_completion` — the finite-dimensional completion-of-the-square identity
  for quadratic forms of symmetric matrices.
* `posDef_precision_add` — `Q + A` is positive definite (hence invertible) when
  `Q` is positive definite and `A` positive semidefinite.
* `selected_mean_spec` — the selected mean `(Q+A)⁻¹(Qμ+b)` solves the normal
  equation `(Q+A) m = Qμ + b`.
* `density_proportional` — the core Gaussian-selection identity: the product of the Gaussian
  density and the selection weight equals a positive constant times the Gaussian
  density with precision `Q+A` and mean `(Q+A)⁻¹(Qμ+b)`.
* `density_normalization_unique`, `selection_total_mass`,
  `selection_posterior_eq_gaussian` — the probability-density normalization
  argument: the selection-weighted density, divided by its total mass, is exactly
  the new Gaussian.

Transpose / dimension conventions are kept explicit; matrix commutativity is
never assumed.
-/

/-! ## Milestone 1 : scalar completion of the square -/

/-- Scalar one-dimensional completion-of-the-square core, a first formal milestone.

For a scalar Gaussian precision `q > 0`, a scalar quadratic-tilt coefficient
`a ≥ 0`, and a linear-tilt coefficient `b`, the exponent
`-½ q (x-μ)² - ½ a x² + b x` completes to `-½ r (x-m)² + K` with new precision
`r = q + a`, new mean `m = (qμ + b)/r`, and an `x`-independent constant `K`. -/
theorem scalar_gaussian_tilt_completion
    (q a μ b x : ℝ)
    (hq : 0 < q) (ha : 0 ≤ a) :
    let r := q + a;
    let m := (q * μ + b) / r;
    -((q * (x - μ)^2) / 2) - (a * x^2 / 2) + b * x =
      -(r * (x - m)^2 / 2) +
        (-(q * μ^2 / 2) + r * m^2 / 2) := by
  intro r m
  have hr : 0 < r := by positivity
  have hrne : r ≠ 0 := ne_of_gt hr
  simp only [m, r]
  field_simp
  ring

/-! ## Bilinear / quadratic-form helper lemmas -/

variable {n : ℕ}

/-- Quadratic form `xᵀ M x` associated with a matrix `M`. -/
noncomputable def qform (M : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) : ℝ :=
  x ⬝ᵥ (M *ᵥ x)

/-- Symmetry of the bilinear form of a symmetric matrix: `xᵀ M y = yᵀ M x`. -/
theorem dp_symm (M : Matrix (Fin n) (Fin n) ℝ) (hM : Mᵀ = M) (x y : Fin n → ℝ) :
    x ⬝ᵥ (M *ᵥ y) = y ⬝ᵥ (M *ᵥ x) := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hM, dotProduct_comm]

/-- Additivity of quadratic forms in the matrix argument:
`xᵀ (Q + A) x = xᵀ Q x + xᵀ A x`. -/
theorem qform_add_split (Q A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    qform (Q + A) x = qform Q x + qform A x := by
  unfold qform
  rw [Matrix.add_mulVec, dotProduct_add]

/-- Expansion of a quadratic form on a difference, using symmetry to merge the
cross terms: `(x-y)ᵀ M (x-y) = xᵀ M x - 2 yᵀ M x + yᵀ M y`. -/
theorem qform_sub_symm (M : Matrix (Fin n) (Fin n) ℝ) (hM : Mᵀ = M) (x y : Fin n → ℝ) :
    qform M (x - y) = qform M x - 2 * (y ⬝ᵥ (M *ᵥ x)) + qform M y := by
  unfold qform
  rw [Matrix.mulVec_sub, dotProduct_sub, sub_dotProduct, sub_dotProduct, dp_symm M hM x y]
  ring

/-! ## Finite-dimensional completion of the square -/

/-- **Matrix completion of the square.**

Let `Q` and `A` be symmetric matrices and let `mstar` solve the normal equation
`(Q + A) mstar = Q μ + b`.  Then for every `x`,
`-½ (x-μ)ᵀ Q (x-μ) - ½ xᵀ A x + bᵀ x = -½ (x-mstar)ᵀ (Q+A) (x-mstar) + K`,
where `K = -½ μᵀ Q μ + ½ mstarᵀ (Q+A) mstar` does not depend on `x`.

No positive-definiteness is needed for the algebraic identity — only symmetry of
`Q`, `A` and the normal equation for `mstar`. -/
theorem matrix_completion
    (Q A : Matrix (Fin n) (Fin n) ℝ) (μ b x mstar : Fin n → ℝ)
    (hQ : Qᵀ = Q) (hA : Aᵀ = A)
    (hmstar : (Q + A) *ᵥ mstar = Q *ᵥ μ + b) :
    - qform Q (x - μ) / 2 - qform A x / 2 + b ⬝ᵥ x
      = - qform (Q + A) (x - mstar) / 2
        + (- qform Q μ / 2 + qform (Q + A) mstar / 2) := by
  have hP : (Q + A)ᵀ = Q + A := by rw [Matrix.transpose_add, hQ, hA]
  have hlin : μ ⬝ᵥ (Q *ᵥ x) + b ⬝ᵥ x = mstar ⬝ᵥ ((Q + A) *ᵥ x) := by
    rw [dp_symm (Q + A) hP mstar x, hmstar, dotProduct_add, dp_symm Q hQ μ x,
      dotProduct_comm b x]
  rw [qform_sub_symm Q hQ x μ, qform_sub_symm (Q + A) hP x mstar, qform_add_split Q A x,
    ← hlin]
  ring

/-! ## Positive definiteness of the tilted precision and the selected mean -/

/-- The tilted precision `Q + A` is positive definite (hence invertible) whenever
`Q` is positive definite and `A` is positive semidefinite. -/
theorem posDef_precision_add
    (Q A : Matrix (Fin n) (Fin n) ℝ) (hQ : Q.PosDef) (hA : A.PosSemidef) :
    (Q + A).PosDef :=
  hQ.add_posSemidef hA

/-- The selected mean `(Q+A)⁻¹ (Qμ + b)` solves the normal equation
`(Q + A) m = Q μ + b`. -/
theorem selected_mean_spec
    (Q A : Matrix (Fin n) (Fin n) ℝ) (μ b : Fin n → ℝ)
    (hQ : Q.PosDef) (hA : A.PosSemidef) :
    (Q + A) *ᵥ ((Q + A)⁻¹ *ᵥ (Q *ᵥ μ + b)) = Q *ᵥ μ + b := by
  have hPpd : (Q + A).PosDef := hQ.add_posSemidef hA
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv, Matrix.one_mulVec]
  exact Ne.isUnit (ne_of_gt hPpd.det_pos)

/-! ## Gaussian densities and the selection weight -/

/-- Multivariate Gaussian density in **precision form**: precision matrix `P`,
mean `m`.  The normalizing constant is `√(det P / (2π)ⁿ)`. -/
noncomputable def gaussianPDF (P : Matrix (Fin n) (Fin n) ℝ) (m x : Fin n → ℝ) : ℝ :=
  Real.sqrt (P.det / (2 * Real.pi) ^ n) * Real.exp (- qform P (x - m) / 2)

/-- Positive coordinate-separable exponential-quadratic selection weight
`w(x) = exp(-½ xᵀ A x + bᵀ x)`. -/
noncomputable def selWeight (A : Matrix (Fin n) (Fin n) ℝ) (b x : Fin n → ℝ) : ℝ :=
  Real.exp (- qform A x / 2 + b ⬝ᵥ x)

/-- The selection weight is strictly positive everywhere. -/
theorem selWeight_pos (A : Matrix (Fin n) (Fin n) ℝ) (b x : Fin n → ℝ) :
    0 < selWeight A b x := Real.exp_pos _

/-! ## Gaussian selection weight preserves Gaussian form -/

/-- **Gaussian-preserving exponential-quadratic self-masking.**

Multiplying the Gaussian density with precision `Q` and mean `μ` by the positive
exponential-quadratic selection weight `exp(-½ xᵀ A x + bᵀ x)` yields a positive
constant multiple of the Gaussian density with precision `Q + A` and mean
`(Q + A)⁻¹ (Q μ + b)`.  Thus the selected density is again Gaussian, with the
stated precision and mean. -/
theorem density_proportional
    (Q A : Matrix (Fin n) (Fin n) ℝ) (μ b : Fin n → ℝ)
    (hQ : Q.PosDef) (hA : A.PosSemidef) :
    ∃ Z : ℝ, 0 < Z ∧ ∀ x : Fin n → ℝ,
      gaussianPDF Q μ x * selWeight A b x
        = Z * gaussianPDF (Q + A) ((Q + A)⁻¹ *ᵥ (Q *ᵥ μ + b)) x := by
  set P := Q + A with hPdef
  have hPpd : P.PosDef := hQ.add_posSemidef hA
  have hQsymm : Qᵀ = Q := by
    have h := hQ.isHermitian
    rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at h
    exact h
  have hAsymm : Aᵀ = A := by
    have h := hA.isHermitian
    rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at h
    exact h
  set mstar := P⁻¹ *ᵥ (Q *ᵥ μ + b) with hmdef
  have hmstar : P *ᵥ mstar = Q *ᵥ μ + b := by
    rw [hmdef, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv, Matrix.one_mulVec]
    exact Ne.isUnit (ne_of_gt hPpd.det_pos)
  have hpipos : (0 : ℝ) < (2 * Real.pi) ^ n := by positivity
  set K := - qform Q μ / 2 + qform P mstar / 2 with hKdef
  refine ⟨Real.sqrt (Q.det / (2 * Real.pi) ^ n) * Real.exp K
      / Real.sqrt (P.det / (2 * Real.pi) ^ n), ?_, ?_⟩
  · apply div_pos
    · apply mul_pos
      · exact Real.sqrt_pos.mpr (div_pos hQ.det_pos hpipos)
      · exact Real.exp_pos K
    · exact Real.sqrt_pos.mpr (div_pos hPpd.det_pos hpipos)
  · intro x
    have hcomp := matrix_completion Q A μ b x mstar hQsymm hAsymm hmstar
    rw [← hPdef] at hcomp
    have hprod : Real.exp (- qform Q (x - μ) / 2) * Real.exp (- qform A x / 2 + b ⬝ᵥ x)
        = Real.exp K * Real.exp (- qform P (x - mstar) / 2) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      rw [hKdef]
      linarith [hcomp]
    have hsP : Real.sqrt (P.det / (2 * Real.pi) ^ n) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.mpr (div_pos hPpd.det_pos hpipos))
    unfold gaussianPDF selWeight
    rw [mul_assoc, hprod]
    field_simp

/-! ## Probability-density normalization argument -/

/-- **Normalization uniqueness.**  If two integrable probability densities are
pointwise proportional (`f = c • g`) and each integrates to `1`, then the
proportionality constant is `1`.  This is the abstract normalization principle:
a probability density proportional to a given one must coincide with it. -/
theorem density_normalization_unique
    {E : Type*} [MeasurableSpace E] {ν : Measure E}
    (f g : E → ℝ) (c : ℝ)
    (hfg : ∀ x, f x = c * g x)
    (hf : ∫ x, f x ∂ν = 1) (hg : ∫ x, g x ∂ν = 1) : c = 1 := by
  have hmass : (1 : ℝ) = c * 1 := by
    calc (1 : ℝ) = ∫ x, f x ∂ν := hf.symm
      _ = ∫ x, c * g x ∂ν := by simp_rw [hfg]
      _ = c * ∫ x, g x ∂ν := by rw [integral_const_mul]
      _ = c * 1 := by rw [hg]
  linarith

/-- **Total mass of the selection-weighted density.**  Given the pointwise
proportionality `product = Z • gaussian` and that the target Gaussian is a
normalized probability density (`∫ gaussian = 1`), the total mass of the
selection-weighted density equals the constant `Z`. -/
theorem selection_total_mass
    {ν : Measure (Fin n → ℝ)}
    (Q A : Matrix (Fin n) (Fin n) ℝ) (μ b : Fin n → ℝ) (Z : ℝ)
    (hprop : ∀ x, gaussianPDF Q μ x * selWeight A b x
        = Z * gaussianPDF (Q + A) ((Q + A)⁻¹ *ᵥ (Q *ᵥ μ + b)) x)
    (hnorm : ∫ x, gaussianPDF (Q + A) ((Q + A)⁻¹ *ᵥ (Q *ᵥ μ + b)) x ∂ν = 1) :
    ∫ x, gaussianPDF Q μ x * selWeight A b x ∂ν = Z := by
  calc ∫ x, gaussianPDF Q μ x * selWeight A b x ∂ν
      = ∫ x, Z * gaussianPDF (Q + A) ((Q + A)⁻¹ *ᵥ (Q *ᵥ μ + b)) x ∂ν := by
        simp_rw [hprop]
    _ = Z * ∫ x, gaussianPDF (Q + A) ((Q + A)⁻¹ *ᵥ (Q *ᵥ μ + b)) x ∂ν := by
        rw [integral_const_mul]
    _ = Z := by rw [hnorm, mul_one]

/-- **The normalized selection-weighted density is exactly the new Gaussian.**

Dividing the selection-weighted density by its total mass `Z` (a positive
constant, e.g. produced by `density_proportional`) recovers, pointwise, the
Gaussian density with precision `Q + A` and mean `(Q + A)⁻¹ (Q μ + b)`.  This is
the precise sense in which "multiplying by the selection weight yields another
Gaussian". -/
theorem selection_posterior_eq_gaussian
    (Q A : Matrix (Fin n) (Fin n) ℝ) (μ b : Fin n → ℝ) (Z : ℝ) (hZ : Z ≠ 0)
    (hprop : ∀ x, gaussianPDF Q μ x * selWeight A b x
        = Z * gaussianPDF (Q + A) ((Q + A)⁻¹ *ᵥ (Q *ᵥ μ + b)) x) :
    ∀ x, (gaussianPDF Q μ x * selWeight A b x) / Z
      = gaussianPDF (Q + A) ((Q + A)⁻¹ *ᵥ (Q *ᵥ μ + b)) x := by
  intro x
  rw [hprop x]
  field_simp

/-! ## Exported-theorem axiom traces -/

#print axioms scalar_gaussian_tilt_completion
#print axioms matrix_completion
#print axioms posDef_precision_add
#print axioms selected_mean_spec
#print axioms density_proportional
#print axioms density_normalization_unique
#print axioms selection_total_mass
#print axioms selection_posterior_eq_gaussian

end RecoveryFormal
