import RecoveryFormal.SelectedAndMarkedLaw

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace RecoveryFormal
namespace ConditionalThinning

variable {α : Type*} [MeasurableSpace α]

/-- The iid finite marked-row sample law. -/
noncomputable def markedSampleLaw (μ : Measure α) (w : α → ℝ) (n : ℕ) :
    Measure (MarkedSample α n) :=
  Measure.pi (fun _ : Fin n => markedRowLaw μ w)

/-- Event that exactly the deterministic index set `I` is retained. -/
def patternEvent {n : ℕ} (I : Finset (Fin n)) : Set (MarkedSample α n) :=
  Set.univ.pi (fun i : Fin n =>
    Set.univ ×ˢ ({decide (i ∈ I)} : Set Bool))

/-- A fixed-pattern cylinder also constraining each retained value. -/
def fixedPatternCylinder {n : ℕ} (I : Finset (Fin n)) (A : I → Set α) :
    Set (MarkedSample α n) :=
  Set.univ.pi (fun i : Fin n =>
    if hi : i ∈ I then A ⟨i, hi⟩ ×ˢ ({true} : Set Bool)
    else Set.univ ×ˢ ({false} : Set Bool))

/-- Coordinate description of a fixed-pattern cylinder. -/
theorem fixedPatternCylinder_eq_pi {n : ℕ} (I : Finset (Fin n)) (A : I → Set α) :
    fixedPatternCylinder I A = Set.univ.pi (fun i : Fin n =>
      if hi : i ∈ I then A ⟨i, hi⟩ ×ˢ ({true} : Set Bool)
      else Set.univ ×ˢ ({false} : Set Bool)) := by
  rfl

/-- Measurability of a fixed retention pattern. -/
theorem measurableSet_patternEvent {n : ℕ} (I : Finset (Fin n)) :
    MeasurableSet (patternEvent (α := α) I) := by
  apply MeasurableSet.pi Set.countable_univ
  intro i _
  exact MeasurableSet.univ.prod (measurableSet_singleton _)

/-- Exact fixed-pattern joint rectangle identity under the canonical iid law. -/
theorem fixedPattern_joint_rectangle {n : ℕ}
    (μ : Measure α) [IsProbabilityMeasure μ] (w : α → ℝ)
    (hwmeas : Measurable w) (hw0 : ∀ x, 0 ≤ w x) (hw1 : ∀ x, w x ≤ 1)
    (I : Finset (Fin n)) (A : I → Set α) (hA : ∀ i, MeasurableSet (A i)) :
    markedSampleLaw μ w n (fixedPatternCylinder I A) =
      (∏ i : I, retainedNumerator μ w (A i)) *
        (discardedNumerator μ w Set.univ) ^ (n - I.card) := by
  rw [fixedPatternCylinder_eq_pi]
  unfold markedSampleLaw
  haveI : IsProbabilityMeasure (markedRowLaw μ w) := markedRowLaw_isProbability μ w hwmeas hw0 hw1
  rw [Measure.pi_pi]
  rw [← Finset.prod_sdiff (Finset.subset_univ I)]
  rw [mul_comm]
  refine congrArg₂ (· * ·) ?_ ?_
  · -- Product over I (retained terms)
    rw [← Finset.prod_coe_sort]
    apply Finset.prod_congr rfl
    intro i _
    simp [markedRowLaw_true_cylinder μ w (A i) (hA i)]
  · -- Product over univ \ I (discarded terms)
    have heq : ∀ x ∈ Finset.univ \ I, (markedRowLaw μ w) (if hi : x ∈ I then A ⟨x, hi⟩ ×ˢ {true} else Set.univ ×ˢ {false}) = (discardedNumerator μ w) Set.univ := by
      intro x hx
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hx
      simp [hx, markedRowLaw_false_cylinder]
    rw [Finset.prod_congr rfl heq, Finset.prod_const]
    rw [show Finset.univ \ I = Iᶜ by ext; simp]
    simp [Finset.card_compl]

/-- Exact probability and strict positivity of every deterministic retained set. -/
theorem retainedSet_probability {n : ℕ}
    (μ : Measure α) [IsProbabilityMeasure μ] (w : α → ℝ)
    (hwmeas : Measurable w) (hw0 : ∀ x, 0 ≤ w x) (hw1 : ∀ x, w x ≤ 1)
    (hq0 : retentionMass μ w ≠ 0) (hq1 : retentionMass μ w ≠ 1)
    (I : Finset (Fin n)) :
    markedSampleLaw μ w n (patternEvent I) =
        retentionMass μ w ^ I.card * (1 - retentionMass μ w) ^ (n - I.card) ∧
      0 < markedSampleLaw μ w n (patternEvent I) := by
  have hmass := discardedNumerator_univ μ w hwmeas hw0 hw1
  have hqpos : 0 < retentionMass μ w := bot_lt_iff_ne_bot.mpr hq0
  have hqle : retentionMass μ w ≤ 1 := by
    have h := congrArg (fun m : Measure α => m Set.univ)
      (retained_add_discarded μ w hwmeas hw0 hw1)
    simp only [Measure.add_apply, measure_univ] at h
    exact le_of_add_le_left h.le
  have hdisc : 0 < 1 - retentionMass μ w := by
    rw [tsub_pos_iff_lt]
    exact lt_of_le_of_ne hqle hq1
  have hpat : patternEvent (α := α) I =
      fixedPatternCylinder I (fun _ => (Set.univ : Set α)) := by
    ext z
    simp only [patternEvent, fixedPatternCylinder, Set.mem_pi, Set.mem_univ,
      true_implies, Set.mem_prod, Set.mem_singleton_iff]
    constructor <;> intro h i
    · by_cases hi : i ∈ I <;> simp [hi, h i]
    · by_cases hi : i ∈ I <;> simpa [hi] using h i
  rw [hpat, fixedPattern_joint_rectangle μ w hwmeas hw0 hw1 I
    (fun _ => (Set.univ : Set α)) (fun _ => MeasurableSet.univ)]
  simp only [retentionMass, Finset.prod_const, Finset.card_univ, hmass]
  rw [Fintype.card_coe]
  exact ⟨rfl, ENNReal.mul_pos (ne_of_gt (ENNReal.pow_pos hqpos _))
    (ne_of_gt (ENNReal.pow_pos hdisc _))⟩

/-- Full conditional product-law equality given a fixed retained pattern. -/
theorem conditional_fixedPattern_productLaw {n : ℕ}
    (μ : Measure α) [IsProbabilityMeasure μ] (w : α → ℝ)
    (hwmeas : Measurable w) (hw0 : ∀ x, 0 ≤ w x) (hw1 : ∀ x, w x ≤ 1)
    (hq0 : retentionMass μ w ≠ 0) (hqtop : retentionMass μ w ≠ ∞)
    (hq1 : retentionMass μ w ≠ 1) (I : Finset (Fin n)) :
    Measure.map (valuesOn I) ((markedSampleLaw μ w n)[|patternEvent I]) =
      Measure.pi (fun _ : I => selectedLaw μ w) := by
  haveI : IsProbabilityMeasure (selectedLaw μ w) :=
    selectedLaw_isProbability μ w hq0 hqtop
  symm
  apply Measure.pi_eq
  intro A hA
  rw [Measure.map_apply]
  · rw [cond_apply (measurableSet_patternEvent I)]
    have hjoint : patternEvent I ∩ valuesOn I ⁻¹' Set.univ.pi A =
        fixedPatternCylinder I A := by
      ext z
      simp only [patternEvent, fixedPatternCylinder, valuesOn, rowValue,
        Set.mem_inter_iff, Set.mem_preimage, Set.mem_pi, Set.mem_univ,
        true_implies, Set.mem_prod, Set.mem_singleton_iff]
      constructor
      · rintro ⟨hp, hv⟩ i
        by_cases hi : i ∈ I
        · simp [hi, hv ⟨i, hi⟩, hp i]
        · simp [hi, hp i]
      · intro h
        constructor
        · intro i
          by_cases hi : i ∈ I
          · have hz := h i
            have hz' : (z i).1 ∈ A ⟨i, hi⟩ ∧ (z i).2 = true := by
              simpa [hi] using hz
            exact ⟨trivial, by simpa [hi] using hz'.2⟩
          · have hz := h i
            simpa [hi] using hz
        · intro i
          have hz := h i.1
          have hz' : (z i.1).1 ∈ A ⟨i.1, i.2⟩ ∧ (z i.1).2 = true := by
            simpa [i.2] using hz
          simpa using hz'.1
    rw [hjoint, fixedPattern_joint_rectangle μ w hwmeas hw0 hw1 I A hA]
    have hp := (retainedSet_probability μ w hwmeas hw0 hw1 hq0 hq1 I).1
    rw [hp]
    simp_rw [retainedNumerator_eq_mass_smul_selectedLaw μ w hq0 hqtop,
      Measure.smul_apply, smul_eq_mul]
    rw [discardedNumerator_univ μ w hwmeas hw0 hw1]
    rw [Finset.prod_mul_distrib, Finset.prod_const]
    simp only [Finset.card_univ, Fintype.card_coe]
    let q := retentionMass μ w
    let d := (1 - q) ^ (n - I.card)
    have hqpow : q ^ I.card ≠ 0 := pow_ne_zero _ hq0
    have hd : d ≠ 0 := by
      apply pow_ne_zero
      intro hz
      have hqle' : q ≤ 1 := by
        have h := congrArg (fun m : Measure α => m Set.univ)
          (retained_add_discarded μ w hwmeas hw0 hw1)
        simp only [Measure.add_apply, measure_univ] at h
        exact le_of_add_le_left h.le
      have : q = 1 := hqle'.antisymm (tsub_eq_zero_iff_le.mp hz)
      exact hq1 this
    change (q ^ I.card * d)⁻¹ *
      ((q ^ I.card * ∏ x, selectedLaw μ w (A x)) * d) = _
    have hqtop' : q ≠ ∞ := by simpa [q] using hqtop
    have hdtop : d ≠ ∞ := by
      apply ENNReal.pow_ne_top
      exact ENNReal.sub_ne_top (by simp)
    rw [ENNReal.mul_inv (Or.inl hqpow) (Or.inl (ENNReal.pow_ne_top hqtop'))]
    calc
      ((q ^ I.card)⁻¹ * d⁻¹) *
          ((q ^ I.card * ∏ x, selectedLaw μ w (A x)) * d)
          = ((q ^ I.card)⁻¹ * q ^ I.card) * (d⁻¹ * d) *
              (∏ x, selectedLaw μ w (A x)) := by ac_rfl
      _ = ∏ x, selectedLaw μ w (A x) := by
        rw [ENNReal.inv_mul_cancel hqpow (ENNReal.pow_ne_top hqtop'),
          ENNReal.inv_mul_cancel hd hdtop]
        simp
  · exact measurable_pi_lambda _ (fun i : I => by
      exact measurable_fst.comp (measurable_pi_apply i.1))
  · exact MeasurableSet.pi Set.countable_univ (fun i _ => hA i)

end ConditionalThinning
end RecoveryFormal
