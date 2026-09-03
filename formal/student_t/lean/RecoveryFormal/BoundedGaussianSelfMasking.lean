import Mathlib
import RecoveryFormal.FiniteSeparableSelectionCI
import RecoveryFormal.GaussianQuadraticTilt

open Matrix MeasureTheory
open scoped BigOperators

namespace RecoveryFormal
namespace BoundedGaussianMask

variable {p : ℕ}

/-- The explicit retention probability for one coordinate. -/
noncomputable def coordWeight (a b c x : ℝ) : ℝ :=
  c * Real.exp (-(a * x ^ 2) / 2 + b * x)

/-- Scalar completion of the square in the retention exponent. -/
theorem coord_exponent_completion (a b x : ℝ) (ha : 0 < a) :
    -(a * x ^ 2) / 2 + b * x =
      -(a * (x - b / a) ^ 2) / 2 + b ^ 2 / (2 * a) := by
  field_simp
  ring

/-- The exact scalar probability bound obtained by completing the square. -/
theorem coordWeight_mem_Ioc
    {a b c x : ℝ} (ha : 0 < a) (hc : 0 < c)
    (hcmax : c ≤ Real.exp (-(b ^ 2 / (2 * a)))) :
    coordWeight a b c x ∈ Set.Ioc (0 : ℝ) 1 := by
  constructor
  · exact mul_pos hc (Real.exp_pos _)
  · unfold coordWeight
    calc
      c * Real.exp (-(a * x ^ 2) / 2 + b * x)
          ≤ Real.exp (-(b ^ 2 / (2 * a))) *
              Real.exp (-(a * x ^ 2) / 2 + b * x) :=
            mul_le_mul_of_nonneg_right hcmax (Real.exp_pos _).le
      _ = Real.exp (-(a * (x - b / a) ^ 2) / 2) := by
            rw [← Real.exp_add, coord_exponent_completion a b x ha]
            congr 1
            ring
      _ ≤ 1 := by
            rw [← Real.exp_zero]
            apply Real.exp_le_exp.mpr
            exact div_nonpos_of_nonpos_of_nonneg
              (neg_nonpos.mpr (mul_nonneg ha.le (sq_nonneg _))) (by norm_num)

/-- A finite-coordinate retention probability, explicitly defined as a product. -/
noncomputable def queryWeight
    (a b c x : Fin p → ℝ) : ℝ :=
  ∏ k, coordWeight (a k) (b k) (c k) (x k)

/-- A finite product of the coordinate probabilities remains in `(0,1]`. -/
theorem queryWeight_mem_Ioc
    (a b c x : Fin p → ℝ)
    (ha : ∀ k, 0 < a k) (hc : ∀ k, 0 < c k)
    (hcmax : ∀ k, c k ≤ Real.exp (-((b k) ^ 2 / (2 * a k)))) :
    queryWeight a b c x ∈ Set.Ioc (0 : ℝ) 1 := by
  have hcoord : ∀ k, coordWeight (a k) (b k) (c k) (x k) ∈ Set.Ioc (0 : ℝ) 1 := by
    exact fun k => coordWeight_mem_Ioc (ha k) (hc k) (hcmax k)
  simp [Set.mem_Ioc] at hcoord ⊢
  refine ⟨?_, ?_⟩
  · exact Finset.prod_pos fun k _ => hcoord k |>.1
  · exact Finset.prod_le_one (fun k _ => le_of_lt (hcoord k |>.1)) fun k _ => hcoord k |>.2

/-- Exact coordinate separability, exposed as a theorem rather than attributed to
an arbitrary positive-semidefinite quadratic form. -/
theorem queryWeight_exact_separable (a b c x : Fin p → ℝ) :
    queryWeight a b c x = ∏ k, coordWeight (a k) (b k) (c k) (x k) := rfl

/-- The diagonal quadratic form is exactly the sum of its coordinate terms. -/
theorem qform_diagonal (a x : Fin p → ℝ) :
    qform (Matrix.diagonal a) x = ∑ k, a k * (x k) ^ 2 := by
  unfold qform
  simp (config := { decide := true }) only [Matrix.mulVec, dotProduct]
  congr 1
  ext i
  simp [Matrix.diagonal]
  ring

/-- The diagonal Gaussian quadratic tilt weight is exactly the product of the coordinate exponential
quadratic factors (before the explicit constants `c k` are included). -/
theorem selWeight_diagonal_eq_prod (a b x : Fin p → ℝ) :
    selWeight (Matrix.diagonal a) b x =
      ∏ k, Real.exp (-(a k * (x k) ^ 2) / 2 + b k * x k) := by
  unfold selWeight
  rw [qform_diagonal]
  rw [show b ⬝ᵥ x = ∑ k, b k * x k by rfl]
  rw [← Real.exp_sum]
  congr 1
  rw [Finset.sum_add_distrib]
  congr 1
  rw [← Finset.sum_div]
  congr 1
  rw [← Finset.sum_neg_distrib]

/-- Pulling out the per-coordinate constants identifies the bounded mask with
the diagonal exponential-quadratic tilt used by the selected-Gaussian construction. -/
theorem queryWeight_eq_const_mul_selWeight (a b c x : Fin p → ℝ) :
    queryWeight a b c x = (∏ k, c k) * selWeight (Matrix.diagonal a) b x := by
  simp [queryWeight, coordWeight, selWeight_diagonal_eq_prod]
  rw [← Finset.prod_mul_distrib]

/-- A diagonal matrix with strictly positive diagonal is positive definite. -/
theorem diagonal_posDef (a : Fin p → ℝ) (ha : ∀ k, 0 < a k) :
    (Matrix.diagonal a).PosDef := by
  exact Matrix.PosDef.diagonal ha

/-- The standard isotropic Gaussian kernel integral in coordinate space. -/
theorem standard_gaussian_kernel_integral :
    (∫ x : Fin p → ℝ, Real.exp (-(∑ k, (x k) ^ 2) / 2)) =
      (2 * Real.pi) ^ ((p : ℝ) / 2) := by
  rw [← Complex.ofReal_inj]
  rw [← integral_complex_ofReal]
  simp_rw [Complex.ofReal_exp, Complex.ofReal_div, Complex.ofReal_neg,
    Complex.ofReal_sum, Complex.ofReal_pow]
  have h := GaussianFourier.integral_cexp_neg_mul_sum_add
    (ι := Fin p) (b := (1 / 2 : ℂ)) (by norm_num) (fun _ => 0)
  calc
    (∫ x : Fin p → ℝ, Complex.exp ((-∑ k, (x k : ℂ) ^ 2) / (2 : ℂ))) =
        ∫ x : Fin p → ℝ, Complex.exp
          (-(1 / 2 : ℂ) * ∑ k, (x k : ℂ) ^ 2 + ∑ k, (0 : ℂ) * x k) := by
          congr 1
          funext x
          congr 1
          simp
          ring
    _ = (Complex.ofReal Real.pi / (1 / 2 : ℂ)) ^ ((p : ℂ) / 2) := by
          rw [h]
          simp
    _ = Complex.ofReal ((2 * Real.pi) ^ ((p : ℝ) / 2)) := by
          rw [Complex.ofReal_cpow (by positivity)]
          norm_num
          congr 2
          ring

/-- A factorized positive-definite quadratic form is the sum of squares of the
coordinates after the factor map. -/
theorem qform_transpose_mul_self (B : Matrix (Fin p) (Fin p) ℝ) (x : Fin p → ℝ) :
    qform (Bᵀ * B) x = ∑ k, ((B *ᵥ x) k) ^ 2 := by
  unfold qform
  rw [← Matrix.mulVec_mulVec]
  rw [Matrix.dotProduct_mulVec]
  rw [Matrix.vecMul_transpose]
  unfold dotProduct
  congr 1
  ext k
  ring

/-- Change of variables for an invertible matrix, specialized to the standard
Gaussian kernel. -/
theorem gaussian_kernel_integral_comp_mulVec
    (B : Matrix (Fin p) (Fin p) ℝ) (hB : B.det ≠ 0) :
    (∫ x : Fin p → ℝ, Real.exp (-(∑ k, ((B *ᵥ x) k) ^ 2) / 2)) =
      |B.det⁻¹| * (2 * Real.pi) ^ ((p : ℝ) / 2) := by
  let f : (Fin p → ℝ) → ℝ := fun y => Real.exp (-(∑ k, (y k) ^ 2) / 2)
  have hmap := Real.map_matrix_volume_pi_eq_smul_volume_pi hB
  have hmeas : AEMeasurable (Matrix.toLin' B) volume :=
    (Matrix.toLin' B).continuous_of_finiteDimensional.measurable.aemeasurable
  have hf : AEStronglyMeasurable f (Measure.map (Matrix.toLin' B) volume) := by
    apply Continuous.aestronglyMeasurable
    fun_prop
  calc
    (∫ x : Fin p → ℝ, Real.exp (-(∑ k, ((B *ᵥ x) k) ^ 2) / 2)) =
        ∫ x, f (Matrix.toLin' B x) := by rfl
    _ = ∫ y, f y ∂Measure.map (Matrix.toLin' B) volume :=
      (integral_map hmeas hf).symm
    _ = ∫ y, f y ∂(ENNReal.ofReal |B.det⁻¹| • volume) := by rw [hmap]
    _ = (ENNReal.ofReal |B.det⁻¹|).toReal * ∫ y, f y := by
      rw [integral_smul_measure]
      rfl
    _ = |B.det⁻¹| * (2 * Real.pi) ^ ((p : ℝ) / 2) := by
      rw [ENNReal.toReal_ofReal (abs_nonneg _), standard_gaussian_kernel_integral]

/-- Scalar cancellation of the determinant Jacobian and Gaussian normalizing
constant. -/
theorem gaussian_normalization_constant_cancel (d : ℝ) (hd : d ≠ 0) :
    Real.sqrt (d ^ 2 / (2 * Real.pi) ^ p) *
      (|d⁻¹| * (2 * Real.pi) ^ ((p : ℝ) / 2)) = 1 := by
  rw [Real.sqrt_div (sq_nonneg d)]
  rw [Real.sqrt_sq_eq_abs]
  have hbase : 0 < 2 * Real.pi := by positivity
  have hsqrtpow : Real.sqrt ((2 * Real.pi) ^ p) =
      (2 * Real.pi) ^ ((p : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast]
    rw [← Real.rpow_mul hbase.le]
    congr 1
    ring
  rw [hsqrtpow]
  field_simp
  simp [one_div, abs_inv, hd]

/-- Isolated multivariate Gaussian integral/normalization theorem used by the
self-masking result.  Here `volume` is Lebesgue measure on `Fin p → ℝ`. -/
theorem gaussianPDF_integral_eq_one
    (P : Matrix (Fin p) (Fin p) ℝ) (m : Fin p → ℝ) (hP : P.PosDef) :
    ∫ x, gaussianPDF P m x = 1 := by
  obtain ⟨B, hBunit, hPB⟩ := Matrix.posDef_iff_eq_conjTranspose_mul_self.mp hP
  have hBdet : B.det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det B).mp hBunit).ne_zero
  have hPB' : P = Bᵀ * B := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using hPB
  have hdet : P.det = B.det ^ 2 := by
    rw [hPB', Matrix.det_mul, Matrix.det_transpose]
    ring
  unfold gaussianPDF
  rw [integral_const_mul]
  have htranslate :
      (∫ x : Fin p → ℝ, Real.exp (-qform P (x - m) / 2)) =
        ∫ x : Fin p → ℝ, Real.exp (-qform P x / 2) := by
    exact integral_sub_right_eq_self (fun x : Fin p → ℝ => Real.exp (-qform P x / 2)) m
  rw [htranslate]
  have hkernel :
      (∫ x : Fin p → ℝ, Real.exp (-qform P x / 2)) =
        |B.det⁻¹| * (2 * Real.pi) ^ ((p : ℝ) / 2) := by
    rw [hPB']
    simp_rw [qform_transpose_mul_self]
    exact gaussian_kernel_integral_comp_mulVec B hBdet
  rw [hkernel, hdet]
  exact gaussian_normalization_constant_cancel B.det hBdet

/-- The weighted density is pointwise proportional to the Gaussian obtained by
instantiating the exponential-quadratic tilt with the diagonal matrix `diagonal a`. -/
theorem bounded_density_proportional
    (Q : Matrix (Fin p) (Fin p) ℝ) (μ a b c : Fin p → ℝ)
    (hQ : Q.PosDef) (ha : ∀ k, 0 < a k) (hc : ∀ k, 0 < c k) :
    ∃ Z : ℝ, 0 < Z ∧ ∀ x,
      gaussianPDF Q μ x * queryWeight a b c x =
        Z * gaussianPDF (Q + Matrix.diagonal a)
          ((Q + Matrix.diagonal a)⁻¹ *ᵥ (Q *ᵥ μ + b)) x := by
  obtain ⟨Z, hZ, hprop⟩ := density_proportional Q (Matrix.diagonal a) μ b hQ
    (diagonal_posDef a ha).posSemidef
  refine ⟨(∏ k, c k) * Z,
    mul_pos (Finset.prod_pos fun k _ => hc k) hZ, ?_⟩
  intro x
  rw [queryWeight_eq_const_mul_selWeight]
  calc
    gaussianPDF Q μ x * ((∏ k, c k) * selWeight (Matrix.diagonal a) b x) =
        (∏ k, c k) * (gaussianPDF Q μ x * selWeight (Matrix.diagonal a) b x) := by ring
    _ = (∏ k, c k) * (Z * gaussianPDF (Q + Matrix.diagonal a)
          ((Q + Matrix.diagonal a)⁻¹ *ᵥ (Q *ᵥ μ + b)) x) := by rw [hprop x]
    _ = ((∏ k, c k) * Z) * gaussianPDF (Q + Matrix.diagonal a)
          ((Q + Matrix.diagonal a)⁻¹ *ᵥ (Q *ᵥ μ + b)) x := by ring

/-- **Exact stated theorem (selected-law transfer).**

For positive diagonal coefficients and explicit constants satisfying the sharp
completion-of-the-square bound, every coordinate mask and their finite product
are valid probabilities.  The mask is exactly coordinate-separable.  For a
Gaussian with positive-definite precision `Q`, retention has finite positive
normalizer `Z`, and its normalized selected density is exactly Gaussian with
precision `Q + diagonal a` and mean
`(Q + diagonal a)⁻¹ (Q μ + b)`. -/
theorem bounded_gaussian_self_masking
    (Q : Matrix (Fin p) (Fin p) ℝ) (μ a b c : Fin p → ℝ)
    (hQ : Q.PosDef)
    (ha : ∀ k, 0 < a k) (hc : ∀ k, 0 < c k)
    (hcmax : ∀ k, c k ≤ Real.exp (-((b k) ^ 2 / (2 * a k)))) :
    (∀ k x, coordWeight (a k) (b k) (c k) x ∈ Set.Ioc (0 : ℝ) 1) ∧
    (∀ x, queryWeight a b c x ∈ Set.Ioc (0 : ℝ) 1) ∧
    (∀ x, queryWeight a b c x =
      ∏ k, coordWeight (a k) (b k) (c k) (x k)) ∧
    ∃ Z : ℝ, 0 < Z ∧
      (∫ x, gaussianPDF Q μ x * queryWeight a b c x) = Z ∧
      (∀ x, (gaussianPDF Q μ x * queryWeight a b c x) / Z =
        gaussianPDF (Q + Matrix.diagonal a)
          ((Q + Matrix.diagonal a)⁻¹ *ᵥ (Q *ᵥ μ + b)) x) := by
  refine ⟨fun k x => coordWeight_mem_Ioc (ha k) (hc k) (hcmax k),
    fun x => queryWeight_mem_Ioc a b c x ha hc hcmax,
    fun x => queryWeight_exact_separable a b c x, ?_⟩
  obtain ⟨Z, hZ, hprop⟩ := bounded_density_proportional Q μ a b c hQ ha hc
  refine ⟨Z, hZ, ?_, ?_⟩
  · calc
      (∫ x, gaussianPDF Q μ x * queryWeight a b c x) =
          ∫ x, Z * gaussianPDF (Q + Matrix.diagonal a)
            ((Q + Matrix.diagonal a)⁻¹ *ᵥ (Q *ᵥ μ + b)) x := by
              congr 1
              funext x
              exact hprop x
      _ = Z * ∫ x, gaussianPDF (Q + Matrix.diagonal a)
            ((Q + Matrix.diagonal a)⁻¹ *ᵥ (Q *ᵥ μ + b)) x := by
              rw [integral_const_mul]
      _ = Z := by
        rw [gaussianPDF_integral_eq_one]
        · ring
        · exact hQ.add_posSemidef (diagonal_posDef a ha).posSemidef
  · intro x
    rw [hprop x]
    field_simp

#print axioms coord_exponent_completion
#print axioms coordWeight_mem_Ioc
#print axioms queryWeight_mem_Ioc
#print axioms queryWeight_exact_separable
#print axioms qform_diagonal
#print axioms selWeight_diagonal_eq_prod
#print axioms queryWeight_eq_const_mul_selWeight
#print axioms diagonal_posDef
#print axioms standard_gaussian_kernel_integral
#print axioms qform_transpose_mul_self
#print axioms gaussian_kernel_integral_comp_mulVec
#print axioms gaussian_normalization_constant_cancel
#print axioms gaussianPDF_integral_eq_one
#print axioms bounded_density_proportional
#print axioms bounded_gaussian_self_masking

end BoundedGaussianMask
end RecoveryFormal
