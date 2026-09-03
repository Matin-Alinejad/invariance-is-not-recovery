import RecoveryFormal.GaussianQuadraticTilt

namespace RecoveryFormal

/-- Gaussian-preserving selection: an already normalized positive selection-weighted Gaussian kernel is
exactly its Gaussian target.  The proportionality premise is exported by
`density_proportional`; normalization removes its positive constant. -/
theorem selected_density_eq_gaussian
    {d : ℕ} (Q A : Matrix (Fin d) (Fin d) ℝ) (mean b targetMean : Fin d → ℝ)
    (Z : ℝ) (hZ : Z ≠ 0)
    (hprop : ∀ x, gaussianPDF Q mean x * selWeight A b x =
      Z * gaussianPDF (Q + A) targetMean x) :
    ∀ x, (gaussianPDF Q mean x * selWeight A b x) / Z =
      gaussianPDF (Q + A) targetMean x := by
  intro x
  rw [hprop x]
  exact mul_div_cancel_left₀ _ hZ

#print axioms selected_density_eq_gaussian
end RecoveryFormal
