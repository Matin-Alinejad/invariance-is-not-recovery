import RecoveryFormal.FixedPattern

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal BigOperators

namespace RecoveryFormal
namespace ConditionalThinning

variable {α : Type*} [MeasurableSpace α]

/-- The measurable event that exactly `m` rows are retained, expressed as the
finite disjoint union of canonical fixed-pattern events. -/
def countEvent {n : ℕ} (m : ℕ) : Set (MarkedSample α n) :=
  ⋃ I ∈ Finset.powersetCard m (Finset.univ : Finset (Fin n)), patternEvent I

/-- The count event is measurable. -/
theorem measurableSet_countEvent {n m : ℕ} :
    MeasurableSet (countEvent (α := α) (n := n) m) := by
  unfold countEvent
  exact Finset.measurableSet_biUnion _ (fun I _ => measurableSet_patternEvent I)

/-- Canonical increasing reindexing of a fixed retained set of size `m`. -/
def orderedValuesOn {n m : ℕ} (I : Finset (Fin n)) (hI : I.card = m)
    (z : MarkedSample α n) : Fin m → α :=
  fun k => rowValue z (I.orderIsoOfFin hI k).1

/-- Joint law on each size-`m` component after increasing-index reindexing. -/
theorem conditional_pattern_ordered_productLaw {n m : ℕ}
    (μ : Measure α) [IsProbabilityMeasure μ] (w : α → ℝ)
    (hwmeas : Measurable w) (hw0 : ∀ x, 0 ≤ w x) (hw1 : ∀ x, w x ≤ 1)
    (hq0 : retentionMass μ w ≠ 0) (hqtop : retentionMass μ w ≠ ∞)
    (hq1 : retentionMass μ w ≠ 1)
    (I : Finset (Fin n)) (hI : I.card = m) :
    Measure.map (orderedValuesOn I hI) ((markedSampleLaw μ w n)[|patternEvent I]) =
      Measure.pi (fun _ : Fin m => selectedLaw μ w) := by
  classical
  haveI : IsProbabilityMeasure (selectedLaw μ w) :=
    selectedLaw_isProbability μ w hq0 hqtop
  let e : I ≃ Fin m := (I.orderIsoOfFin hI).toEquiv.symm
  let R : (I → α) → (Fin m → α) :=
    MeasurableEquiv.piCongrLeft (fun _ : Fin m => α) e
  have hvalues : Measurable (valuesOn I : MarkedSample α n → (I → α)) := by
    exact measurable_pi_lambda _ (fun i : I =>
      measurable_fst.comp (measurable_pi_apply i.1))
  have hR : Measurable R := by
    exact (MeasurableEquiv.piCongrLeft (fun _ : Fin m => α) e).measurable
  have hfun : orderedValuesOn I hI = R ∘ valuesOn I := by
    funext z k
    change rowValue z (I.orderIsoOfFin hI k).1 =
      (MeasurableEquiv.piCongrLeft (fun _ : Fin m => α) e) (valuesOn I z) k
    rw [show k = e (e.symm k) by simp]
    rw [MeasurableEquiv.piCongrLeft_apply_apply]
    simp [e, valuesOn, rowValue]
  rw [hfun, ← MeasureTheory.Measure.map_map hR hvalues,
    conditional_fixedPattern_productLaw μ w hwmeas hw0 hw1 hq0 hqtop hq1 I]
  simpa [R, e] using
    (MeasureTheory.Measure.pi_map_piCongrLeft e (fun _ : Fin m => selectedLaw μ w))

/-- The retained count has the exact binomial pmf, derived by summing pattern
probabilities. -/
theorem retainedCount_binomial {n k : ℕ}
    (μ : Measure α) [IsProbabilityMeasure μ] (w : α → ℝ)
    (hwmeas : Measurable w) (hw0 : ∀ x, 0 ≤ w x) (hw1 : ∀ x, w x ≤ 1)
    (hq0 : retentionMass μ w ≠ 0) (hq1 : retentionMass μ w ≠ 1) :
    markedSampleLaw μ w n (countEvent k) =
      (n.choose k : ℝ≥0∞) * retentionMass μ w ^ k *
        (1 - retentionMass μ w) ^ (n - k) := by
  classical
  rw [countEvent, measure_biUnion_finset]
  · rw [Finset.sum_congr rfl fun I hI => by
        rw [(retainedSet_probability μ w hwmeas hw0 hw1 hq0 hq1 I).1,
          (Finset.mem_powersetCard.mp hI).2]]
    rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    ring
  · intro I _ J _ hIJ
    simp only [Function.onFun, Set.disjoint_left]
    rintro z hzI hzJ
    apply hIJ
    ext r
    simp only [patternEvent, Set.mem_pi, Set.mem_univ, true_implies,
      Set.mem_prod, Set.mem_singleton_iff] at hzI hzJ
    exact decide_eq_decide.mp ((hzI r).2.symm.trans (hzJ r).2)
  · intro I _
    exact measurableSet_patternEvent I

/-- A measurable function agreeing with increasing-index ordering on every
size-`m` fixed-pattern component. -/
lemma exists_measurable_ordered_retainedVector {n m : ℕ}
    (μ : Measure α) [IsProbabilityMeasure μ] :
    ∃ v : MarkedSample α n → Fin m → α, Measurable v ∧
      ∀ I : Finset (Fin n), ∀ hI : I.card = m,
        Set.EqOn v (orderedValuesOn I hI) (patternEvent I)  := by
  classical
  let x0 : α := Classical.choice (nonempty_of_isProbabilityMeasure μ)
  let T := Finset.powersetCard m (Finset.univ : Finset (Fin n))
  have hind : ∀ S : Finset (Finset (Fin n)), S ⊆ T →
      ∃ v : MarkedSample α n → Fin m → α, Measurable v ∧
        ∀ I ∈ S, ∀ hI : I.card = m,
          Set.EqOn v (orderedValuesOn I hI) (patternEvent I) := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
        intro _
        refine ⟨fun _ _ => x0, measurable_const, ?_⟩
        simp
    | @insert I S hIS ih =>
        intro hsub
        have hIT : I ∈ T := hsub (Finset.mem_insert_self I S)
        have hcard : I.card = m := (Finset.mem_powersetCard.mp hIT).2
        obtain ⟨v, hvmeas, hv⟩ := ih (fun J hJ => hsub (Finset.mem_insert_of_mem hJ))
        let oi : MarkedSample α n → Fin m → α := orderedValuesOn I hcard
        let v' : MarkedSample α n → Fin m → α :=
          (patternEvent I).piecewise oi v
        have hoimeas : Measurable oi := by
          unfold oi orderedValuesOn
          exact measurable_pi_lambda _ (fun k =>
            measurable_fst.comp (measurable_pi_apply ((I.orderIsoOfFin hcard) k).1))
        have hv'meas : Measurable v' :=
          hoimeas.piecewise (measurableSet_patternEvent I) hvmeas
        refine ⟨v', hv'meas, ?_⟩
        intro J hJ hJcard z hzJ
        simp only [Finset.mem_insert] at hJ
        rcases hJ with rfl | hJS
        · simp [v', oi, hzJ]
        · have hJI : J ≠ I := by
            intro h
            subst J
            exact hIS hJS
          have hznot : z ∉ patternEvent I := by
            intro hzI
            apply hJI
            ext r
            simp only [patternEvent, Set.mem_pi, Set.mem_univ, true_implies,
              Set.mem_prod, Set.mem_singleton_iff] at hzJ hzI
            exact decide_eq_decide.mp ((hzJ r).2.symm.trans (hzI r).2)
          simp [v', hznot, hv J hJS hJcard hzJ]
  obtain ⟨v, hvmeas, hv⟩ := hind T (fun _ h => h)
  refine ⟨v, hvmeas, ?_⟩
  intro I hI
  apply hv I
  · exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ I, hI⟩


/-- Joint rectangle probability on a size-`m` pattern, expressed using the
ordered coordinates. -/
lemma fixedPattern_ordered_rectangle {n m : ℕ}
    (μ : Measure α) [IsProbabilityMeasure μ] (w : α → ℝ)
    (hwmeas : Measurable w) (hw0 : ∀ x, 0 ≤ w x) (hw1 : ∀ x, w x ≤ 1)
    (hq0 : retentionMass μ w ≠ 0) (hqtop : retentionMass μ w ≠ ∞)
    (hq1 : retentionMass μ w ≠ 1)
    (I : Finset (Fin n)) (hI : I.card = m)
    (A : Fin m → Set α) (hA : ∀ i, MeasurableSet (A i)) :
    markedSampleLaw μ w n
        (patternEvent I ∩ orderedValuesOn I hI ⁻¹' Set.univ.pi A) =
      markedSampleLaw μ w n (patternEvent I) *
        ∏ i, selectedLaw μ w (A i)  := by
  have hmeas : Measurable (orderedValuesOn I hI : MarkedSample α n → (Fin m → α)) := by
    unfold orderedValuesOn
    exact measurable_pi_lambda _ (fun k =>
      measurable_fst.comp (measurable_pi_apply ((I.orderIsoOfFin hI) k).1))
  have hpi : MeasurableSet (Set.univ.pi A) := MeasurableSet.univ_pi hA
  have hlaw := congrArg (fun ν : Measure (Fin m → α) => ν (Set.univ.pi A))
    (conditional_pattern_ordered_productLaw μ w hwmeas hw0 hw1 hq0 hqtop hq1 I hI)
  change (Measure.map (orderedValuesOn I hI) ((markedSampleLaw μ w n)[|patternEvent I]))
      (Set.univ.pi A) = (Measure.pi fun _ : Fin m => selectedLaw μ w) (Set.univ.pi A) at hlaw
  rw [Measure.map_apply hmeas hpi, cond_apply (measurableSet_patternEvent I)] at hlaw
  haveI : IsProbabilityMeasure (selectedLaw μ w) :=
    selectedLaw_isProbability μ w hq0 hqtop
  rw [Measure.pi_pi] at hlaw
  have hp := retainedSet_probability μ w hwmeas hw0 hw1 hq0 hq1 I
  have hp0 : markedSampleLaw μ w n (patternEvent I) ≠ 0 := ne_of_gt hp.2
  have hpTop : markedSampleLaw μ w n (patternEvent I) ≠ ∞ := by
    rw [hp.1]
    exact ENNReal.mul_ne_top (ENNReal.pow_ne_top hqtop)
      (ENNReal.pow_ne_top (ENNReal.sub_ne_top (by simp)))
  calc
    markedSampleLaw μ w n
        (patternEvent I ∩ orderedValuesOn I hI ⁻¹' Set.univ.pi A)
        = markedSampleLaw μ w n (patternEvent I) *
          ((markedSampleLaw μ w n (patternEvent I))⁻¹ *
            markedSampleLaw μ w n
              (patternEvent I ∩ orderedValuesOn I hI ⁻¹' Set.univ.pi A)) := by
            rw [← mul_assoc, ENNReal.mul_inv_cancel hp0 hpTop, one_mul]
    _ = markedSampleLaw μ w n (patternEvent I) *
          ∏ i, selectedLaw μ w (A i) := by rw [hlaw]


/-- Summing the identical ordered rectangle law over all size-`m` patterns. -/
lemma count_ordered_rectangle {n m : ℕ}
    (μ : Measure α) [IsProbabilityMeasure μ] (w : α → ℝ)
    (hwmeas : Measurable w) (hw0 : ∀ x, 0 ≤ w x) (hw1 : ∀ x, w x ≤ 1)
    (hq0 : retentionMass μ w ≠ 0) (hqtop : retentionMass μ w ≠ ∞)
    (hq1 : retentionMass μ w ≠ 1)
    (v : MarkedSample α n → Fin m → α)
    (hv : ∀ I : Finset (Fin n), ∀ hI : I.card = m,
      Set.EqOn v (orderedValuesOn I hI) (patternEvent I))
    (A : Fin m → Set α) (hA : ∀ i, MeasurableSet (A i)) :
    markedSampleLaw μ w n (countEvent m ∩ v ⁻¹' Set.univ.pi A) =
      markedSampleLaw μ w n (countEvent m) *
        ∏ i, selectedLaw μ w (A i) := by
  classical
  -- Rewrite countEvent as union
  rw [countEvent]
  -- Rewrite the intersection with union as union of intersections
  have h1 : (⋃ I ∈ powersetCard m univ, patternEvent I) ∩ v ⁻¹' Set.univ.pi A =
      ⋃ I ∈ powersetCard m univ, patternEvent I ∩ v ⁻¹' Set.univ.pi A := by
    ext x
    simp [Set.mem_inter_iff, Set.mem_iUnion, Set.mem_preimage]
    tauto
  rw [h1]
  rw [measure_biUnion_finset]
  · -- Main sum equality
    -- Rewrite each term using hv
    have hsum : ∑ p ∈ powersetCard m univ,
        (markedSampleLaw μ w n) (patternEvent p ∩ v ⁻¹' Set.univ.pi A) =
      ∑ p ∈ powersetCard m univ,
        (markedSampleLaw μ w n) (patternEvent p) * ∏ i, (selectedLaw μ w) (A i) := by
      apply Finset.sum_congr rfl
      intro I hIm
      have hIm' : I.card = m := Finset.mem_powersetCard.mp hIm |>.2
      have heq : patternEvent I ∩ v ⁻¹' Set.univ.pi A =
          patternEvent I ∩ (orderedValuesOn I hIm') ⁻¹' Set.univ.pi A := by
        ext x
        simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies]
        constructor
        · rintro ⟨hxI, hxA⟩
          exact ⟨hxI, fun i => (congrArg (fun y => y ∈ A i) (congrFun (hv I hIm' hxI) i)).symm ▸ hxA i⟩
        · rintro ⟨hxI, hxA⟩
          exact ⟨hxI, fun i => (congrArg (fun y => y ∈ A i) (congrFun (hv I hIm' hxI) i)) ▸ hxA i⟩
      rw [heq, fixedPattern_ordered_rectangle μ w hwmeas hw0 hw1 hq0 hqtop hq1 I hIm' A hA]
    rw [hsum]
    rw [← Finset.sum_mul]
    congr 1
    -- Now need to show sum of pattern probabilities = countEvent probability
    rw [← measure_biUnion_finset] <;> try rfl
    · intro I _ J _ hIJ
      simp only [Function.onFun, Set.disjoint_left]
      rintro z hzI hzJ
      apply hIJ
      ext r
      simp only [patternEvent, Set.mem_pi, Set.mem_univ, true_implies,
        Set.mem_prod, Set.mem_singleton_iff] at hzI hzJ
      exact decide_eq_decide.mp ((hzI r).2.symm.trans (hzJ r).2)
    · intro I _
      exact measurableSet_patternEvent I
  · -- Disjointness
    intro I _ J _ hIJ
    simp only [Function.onFun, Set.disjoint_left]
    rintro z ⟨hzI, _⟩ ⟨hzJ, _⟩
    apply hIJ
    ext r
    simp only [patternEvent, Set.mem_pi, Set.mem_univ, true_implies,
      Set.mem_prod, Set.mem_singleton_iff] at hzI hzJ
    exact decide_eq_decide.mp ((hzI r).2.symm.trans (hzJ r).2)
  · -- Measurability
    intro I hIm
    have hIm' : I.card = m := Finset.mem_powersetCard.mp hIm |>.2
    have heq : patternEvent I ∩ v ⁻¹' Set.univ.pi A =
        patternEvent I ∩ (orderedValuesOn I hIm') ⁻¹' Set.univ.pi A := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies]
      constructor
      · rintro ⟨hxI, hxA⟩
        exact ⟨hxI, fun i => (congrArg (fun y => y ∈ A i) (congrFun (hv I hIm' hxI) i)).symm ▸ hxA i⟩
      · rintro ⟨hxI, hxA⟩
        exact ⟨hxI, fun i => by exact congrArg (fun y => y ∈ A i) (congrFun (hv I hIm' hxI) i) ▸ hxA i⟩
    rw [heq]
    let e : I ≃ Fin m := (I.orderIsoOfFin hIm').toEquiv.symm
    let R : (I → α) → (Fin m → α) := MeasurableEquiv.piCongrLeft (fun _ : Fin m => α) e
    have hfun : orderedValuesOn I hIm' = R ∘ valuesOn I := by
      funext z k
      change rowValue z (I.orderIsoOfFin hIm' k).1 =
        (MeasurableEquiv.piCongrLeft (fun _ : Fin m => α) e) (valuesOn I z) k
      rw [show k = e (e.symm k) by simp]
      rw [MeasurableEquiv.piCongrLeft_apply_apply]
      simp [e, valuesOn, rowValue]
    rw [hfun]
    have hvalues : Measurable (valuesOn I : MarkedSample α n → (I → α)) := by
      exact measurable_pi_lambda _ (fun i : I =>
        measurable_fst.comp (measurable_pi_apply i.1))
    have hR : Measurable R := MeasurableEquiv.measurable _
    have hUs : MeasurableSet (Set.univ.pi A) := MeasurableSet.univ_pi hA
    exact MeasurableSet.inter (measurableSet_patternEvent I) (hUs.preimage (hR.comp hvalues))

/-- A measurable ordered retained-vector representative on `{N=m}`. Outside
that event its value is irrelevant; existence is derived from positive selected
mass rather than assumed inhabitedness of the state space. -/
theorem conditional_count_ordered_productLaw {n m : ℕ} (hm : m ≤ n)
    (μ : Measure α) [IsProbabilityMeasure μ] (w : α → ℝ)
    (hwmeas : Measurable w) (hw0 : ∀ x, 0 ≤ w x) (hw1 : ∀ x, w x ≤ 1)
    (hq0 : retentionMass μ w ≠ 0) (hqtop : retentionMass μ w ≠ ∞)
    (hq1 : retentionMass μ w ≠ 1) :
    ∃ retainedVector : MarkedSample α n → Fin m → α,
      Measurable retainedVector ∧
      Measure.map retainedVector ((markedSampleLaw μ w n)[|countEvent m]) =
        Measure.pi (fun _ : Fin m => selectedLaw μ w)  := by
  classical
  obtain ⟨v, hvmeas, hv⟩ :=
    exists_measurable_ordered_retainedVector (α := α) (n := n) (m := m) μ
  refine ⟨v, hvmeas, ?_⟩
  haveI : IsProbabilityMeasure (selectedLaw μ w) :=
    selectedLaw_isProbability μ w hq0 hqtop
  symm
  apply Measure.pi_eq
  intro A hA
  rw [Measure.map_apply hvmeas (MeasurableSet.univ_pi hA)]
  rw [cond_apply measurableSet_countEvent]
  rw [count_ordered_rectangle μ w hwmeas hw0 hw1 hq0 hqtop hq1 v hv A hA]
  let c := markedSampleLaw μ w n (countEvent m)
  have hc : c = (n.choose m : ℝ≥0∞) * retentionMass μ w ^ m *
      (1 - retentionMass μ w) ^ (n - m) :=
    retainedCount_binomial μ w hwmeas hw0 hw1 hq0 hq1
  have hchoose : n.choose m ≠ 0 := Nat.choose_ne_zero hm
  have hqle : retentionMass μ w ≤ 1 := by
    have h := congrArg (fun M : Measure α => M Set.univ)
      (retained_add_discarded μ w hwmeas hw0 hw1)
    simp only [Measure.add_apply, measure_univ] at h
    exact le_of_add_le_left h.le
  have hdisc : 1 - retentionMass μ w ≠ 0 := by
    intro hd
    apply hq1
    exact hqle.antisymm (tsub_eq_zero_iff_le.mp hd)
  have hc0 : c ≠ 0 := by
    rw [hc]
    exact mul_ne_zero (mul_ne_zero (by exact_mod_cast hchoose) (pow_ne_zero _ hq0))
      (pow_ne_zero _ hdisc)
  have hctop : c ≠ ∞ := by
    rw [hc]
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (by simp) (ENNReal.pow_ne_top hqtop))
      (ENNReal.pow_ne_top (ENNReal.sub_ne_top (by simp)))
  change c⁻¹ * (c * ∏ i, selectedLaw μ w (A i)) = _
  rw [← mul_assoc, ENNReal.inv_mul_cancel hc0 hctop, one_mul]



end ConditionalThinning
end RecoveryFormal
