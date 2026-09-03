import RecoveryFormal.GaussianDecomposition
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace RecoveryFormal
namespace GaussianPartialCorrelation

noncomputable def partialCorrT (m s : ℕ) (r : ℝ) : ℝ :=
  r * Real.sqrt ((partialCorrelationDf m s : ℝ) / (1 - r ^ 2))

/-- Exact transformation theorem from the residual normal/chi-square contract.
This is separate from the unformalized derivation of that contract from Gaussian
sample rows. -/
theorem sample_partial_correlation_studentT_of_representation
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (m s : ℕ) (rhat : Ω → ℝ)
    (hrep : HasGaussianResidualRepresentation P m s rhat)
    (hsize : s + 2 < m) :
    Measure.map (fun ω => partialCorrT m s (rhat ω)) P =
      studentTMeasure (partialCorrelationDf m s) := by
  obtain ⟨Z, V, hZm, hVm, hrhatm, hmapZ, hmapV,hindep, hrhat_eq⟩ := hrep
  -- First show that partialCorrT m s (rhat ω) = Z ω / sqrt(V ω / df) a.e.
  have hpartial_eq : ∀ᵐ ω ∂P, partialCorrT m s (rhat ω) = Z ω / Real.sqrt (V ω / (partialCorrelationDf m s : ℝ)) := by
    -- df > 0 since s + 2 < m
    have hdf_pos : 0 < partialCorrelationDf m s := by
      simp [partialCorrelationDf]
      omega
    -- V > 0 a.e. since V ~ chi-square(df) with df > 0
    have hV_pos_ae : ∀ᵐ ω ∂P, 0 < V ω := by
      have hchi := chiSquareMeasure_Iic_zero (partialCorrelationDf m s)
      have hmap_zero : Measure.map V P (Set.Iic 0) = 0 := by rw [hmapV]; exact hchi
      rw [Measure.map_apply hVm measurableSet_Iic] at hmap_zero
      rw [ae_iff]
      convert hmap_zero using 2
      ext x
      simp [le_iff_lt_or_eq]
    filter_upwards [hrhat_eq, hV_pos_ae] with ω hrhat_r hV_pos
    rw [hrhat_r]
    unfold partialCorrT
    -- Z^2 + V > 0 since V > 0
    have hZ2V_pos : 0 < Z ω ^ 2 + V ω := by positivity
    --(df : ℝ) > 0
    have hdf_pos' : (0 : ℝ) < partialCorrelationDf m s := Nat.cast_pos.mpr hdf_pos
    -- Key: (Z / sqrt(Z^2 + V))^2 = Z^2 / (Z^2 + V)
    have hsq : (Z ω / Real.sqrt (Z ω ^ 2 + V ω)) ^ 2 = Z ω ^ 2 / (Z ω ^ 2 + V ω) := by
      rw [div_pow, Real.sq_sqrt (le_of_lt hZ2V_pos)]
    -- 1 - Z^2/(Z^2+V) = V/(Z^2+V)
    have h1_minsq : 1 - Z ω ^ 2 / (Z ω ^ 2 + V ω) = V ω / (Z ω ^ 2 + V ω) := by
      field_simp
      ring
    -- Rewrite the goal using hsq and h1_minsq
    rw [hsq, h1_minsq]
    -- df * (Z^2 + V) / V = (df / V) * (Z^2 + V)
    have hdiv : (partialCorrelationDf m s : ℝ) / (V ω / (Z ω ^ 2 + V ω)) = 
                (partialCorrelationDf m s / V ω) * (Z ω ^ 2 + V ω) := by
      rw [div_div_eq_mul_div]; ring
    rw [hdiv]
    -- sqrt(df/V * (Z^2 + V)) = sqrt(df/V) * sqrt(Z^2 + V)
    have hsqrt_mul : Real.sqrt ((partialCorrelationDf m s / V ω) * (Z ω ^ 2 + V ω)) = 
                     Real.sqrt (partialCorrelationDf m s / V ω) * Real.sqrt (Z ω ^ 2 + V ω) := by
      rw [Real.sqrt_mul (by positivity : 0 ≤ partialCorrelationDf m s / V ω)]
    rw [hsqrt_mul]
    -- Cancel sqrt(Z^2 + V)
    have hsqrt_ne : Real.sqrt (Z ω ^ 2 + V ω) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hZ2V_pos)
    have hcancel : Z ω / Real.sqrt (Z ω ^ 2 + V ω) * (Real.sqrt (partialCorrelationDf m s / V ω) * Real.sqrt (Z ω ^ 2 + V ω)) = 
                   Z ω * Real.sqrt (partialCorrelationDf m s / V ω) := by
      rw [div_mul_eq_mul_div]
      rw [mul_div_assoc]
      rw [mul_div_cancel_right₀ _ hsqrt_ne]
    rw [hcancel]
    -- Now Z * sqrt(df/V) = Z / sqrt(V/df)
    -- sqrt(df/V) = 1 / sqrt(V/df)
    have hsqrt_recip : Real.sqrt (partialCorrelationDf m s / V ω) = 
                       (Real.sqrt (V ω / partialCorrelationDf m s))⁻¹ := by
      rw [Real.sqrt_div (by positivity : (0 : ℝ) ≤ partialCorrelationDf m s)]
      rw [Real.sqrt_div (by positivity : (0 : ℝ) ≤ V ω)]
      field_simp
    rw [hsqrt_recip, div_eq_mul_inv]
    rfl
  -- Now we use hpartial_eq to rewrite the measure
  have hpartial_eq' : (fun ω => partialCorrT m s (rhat ω)) =ᵐ[P] (fun ω => Z ω / Real.sqrt (V ω / (partialCorrelationDf m s : ℝ))) := hpartial_eq
  rw [Measure.map_congr hpartial_eq']
  -- Show that the map of Z/sqrt(V/df) equals studentTMeasure
  unfold studentTMeasure
  -- The key: Measure.map (fun ω => (Z ω, V ω)) P = product measure
  have hjoint : Measure.map (fun ω => (Z ω, V ω)) P = (gaussianReal 0 1).prod (chiSquareMeasure (partialCorrelationDf m s)) := by
    refine Measure.ext_prod ?_
    intro s t hs ht
    rw [Measure.map_apply (hZm.prodMk hVm) (hs.prod ht)]
    -- The preimage of s ×ˢ t under (Z, V) is {ω | Z ω ∈ s ∧ V ω ∈ t}
    have hpre : (fun a => (Z a, V a)) ⁻¹' (s ×ˢ t) = {ω | Z ω ∈ s} ∩ {ω | V ω ∈ t} := by
      ext ω
      simp [Set.mem_preimage, Set.mem_prod]
    rw [hpre]
    -- Use independence: P(Z ∈ s ∧ V ∈ t) = P(Z ∈ s) * P(V ∈ t)
    -- Note: IndepFun uses comap sigma-algebras
    have hmeas_s : MeasurableSet[MeasurableSpace.comap Z Real.measurableSpace] (Z ⁻¹' s) := by
      exact ⟨s, hs, rfl⟩
    have hmeas_t : MeasurableSet[MeasurableSpace.comap V Real.measurableSpace] (V ⁻¹' t) := by
      exact ⟨t, ht, rfl⟩
    have hinde' := hindep (Z ⁻¹' s) (V ⁻¹' t) hmeas_s hmeas_t
    simp only [Kernel.const_apply] at hinde'
    rw [ae_iff] at hinde'
    -- hinde' says dirac () of the bad set is 0, which means the equality holds
    have heq : P (Z ⁻¹' s ∩ V ⁻¹' t) = P (Z ⁻¹' s) * P (V ⁻¹' t) := by
      by_contra hne
      simp [hne] at hinde'
    simp only [Set.preimage] at heq
    rw [heq]
    rw [← hmapZ, ← hmapV]
    rw [Measure.prod_prod s t]
    simp [Measure.map_apply hZm hs, Measure.map_apply hVm ht]
    rfl
  -- Now use hjoint and map composition
  calc Measure.map (fun ω => Z ω / Real.sqrt (V ω / (partialCorrelationDf m s : ℝ))) P
      = Measure.map (fun z : ℝ × ℝ => z.1 / Real.sqrt (z.2 / (partialCorrelationDf m s : ℝ)))
          (Measure.map (fun ω => (Z ω, V ω)) P) := by
        rw [Measure.map_map]
        · rfl
        · fun_prop
        · fun_prop
    _ = Measure.map (fun z : ℝ × ℝ => z.1 / Real.sqrt (z.2 / (partialCorrelationDf m s : ℝ)))
          ((gaussianReal 0 1).prod (chiSquareMeasure (partialCorrelationDf m s))) := by
        rw [hjoint]

/-- Transfer of exact Student-t mass through a measurable statistic. -/
theorem conditional_rejection_probability_eq_alpha
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (T : Ω → ℝ) (df : ℕ)
    (hTm : Measurable T)
    (hT : Measure.map T P = studentTMeasure df)
    (R : Set ℝ) (hR : MeasurableSet R) (α : ℝ≥0∞)
    (hcrit : studentTMeasure df R = α) : P (T ⁻¹' R) = α := by
  rw [← hcrit, ← hT, Measure.map_apply hTm hR]

/-- A two-sided critical region corollary.  The exact mass hypothesis is explicit;
no unproved quantile-existence claim is used. -/
theorem two_sided_rejection_probability_eq_alpha
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (T : Ω → ℝ) (df : ℕ)
    (hTm : Measurable T)
    (hT : Measure.map T P = studentTMeasure df)
    (c : ℝ) (α : ℝ≥0∞)
    (hcrit : studentTMeasure df {x | c ≤ |x|} = α) :
    P (T ⁻¹' {x | c ≤ |x|}) = α := by
  apply conditional_rejection_probability_eq_alpha P T df hTm hT
  · exact measurableSet_le measurable_const measurable_abs
  · exact hcrit

end GaussianPartialCorrelation
end RecoveryFormal
