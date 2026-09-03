import Mathlib
import RecoveryFormal.FiniteSeparableSelectionCI

open scoped BigOperators
namespace RecoveryFormal
namespace FiniteCI

variable {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]

/-- Total mass of a finite (not necessarily normalized) mass function. -/
def totalMass (p : X → Y → Z → ℝ) : ℝ := ∑ x, ∑ y, ∑ z, p x y z

/-- Normalize a finite mass function by its total mass. -/
noncomputable def normalizedMass (p : X → Y → Z → ℝ) : X → Y → Z → ℝ :=
  fun x y z => p x y z / totalMass p

/-- The `Z`-marginal mass. -/
def zMarginal (p : X → Y → Z → ℝ) (z : Z) : ℝ := ∑ x, ∑ y, p x y z

/-- The conditional joint mass of `X,Y` given `Z = z`. -/
noncomputable def conditionalJoint (p : X → Y → Z → ℝ) (x : X) (y : Y) (z : Z) : ℝ :=
  p x y z / zMarginal p z

/-- The conditional `X`-marginal given `Z = z`. -/
noncomputable def conditionalX (p : X → Y → Z → ℝ) (x : X) (z : Z) : ℝ :=
  ∑ y, conditionalJoint p x y z

/-- The conditional `Y`-marginal given `Z = z`. -/
noncomputable def conditionalY (p : X → Y → Z → ℝ) (y : Y) (z : Z) : ℝ :=
  ∑ x, conditionalJoint p x y z

/-- Genuine finite conditional independence, stated as factorization of the
conditional joint mass into its two conditional marginals. -/
def CondIndepMass (p : X → Y → Z → ℝ) : Prop :=
  ∀ x y z, conditionalJoint p x y z = conditionalX p x z * conditionalY p y z

/-- Total unnormalized mass after coordinate-separable selection. -/
def selectedNormalizer (p : X → Y → Z → ℝ)
    (a : X → ℝ) (b : Y → ℝ) (c : Z → ℝ) : ℝ :=
  totalMass (selectedMass p a b c)

/-- The normalized selected finite mass. -/
noncomputable def normalizedSelectedMass (p : X → Y → Z → ℝ)
    (a : X → ℝ) (b : Y → ℝ) (c : Z → ℝ) : X → Y → Z → ℝ :=
  fun x y z => selectedMass p a b c x y z / selectedNormalizer p a b c

omit [Fintype Z] in
lemma zMarginal_pos_of_pos
    (p : X → Y → Z → ℝ) (hpos : ∀ x y z, 0 < p x y z)
    (x : X) (y : Y) (z : Z) : 0 < zMarginal p z := by
  simp only [zMarginal]
  apply Finset.sum_pos
  · intro x' _
    apply Finset.sum_pos
    · intro y' _
      exact hpos x' y' z
    · exact Finset.univ_nonempty_iff.mpr ⟨y⟩
  · exact Finset.univ_nonempty_iff.mpr ⟨x⟩

omit [Fintype Z] in
/-- Algebraic factorization form of finite conditional independence. -/
theorem condIndepMass_iff_factorization
    (p : X → Y → Z → ℝ) (hpos : ∀ x y z, 0 < p x y z) :
    CondIndepMass p ↔
      ∀ x y z, p x y z * zMarginal p z =
        (∑ y', p x y' z) * (∑ x', p x' y z) := by
  constructor
  · intro h x y z
    have hz := zMarginal_pos_of_pos p hpos x y z
    have hi := h x y z
    simp only [CondIndepMass, conditionalJoint, conditionalX, conditionalY] at h hi
    rw [← Finset.sum_div, ← Finset.sum_div] at hi
    field_simp at hi
    nlinarith
  · intro h x y z
    have hz := zMarginal_pos_of_pos p hpos x y z
    have hi := h x y z
    simp only [conditionalJoint, conditionalX, conditionalY]
    rw [← Finset.sum_div, ← Finset.sum_div]
    field_simp
    nlinarith

omit [Fintype Z] in
/-- Normalized finite conditional independence is equivalent to the four-point
(cross-product) criterion from `FiniteSeparableSelectionCI`. -/
theorem condIndepMass_iff_fourPoint
    (p : X → Y → Z → ℝ)
    (hpos : ∀ x y z, 0 < p x y z) :
    CondIndepMass p ↔ FourPointCI p := by
  rw [condIndepMass_iff_factorization p hpos]
  constructor
  · intro h x x' y y' z
    have hz := zMarginal_pos_of_pos p hpos x y z
    have hxy := h x y z
    have hxy' := h x y' z
    have hx'y := h x' y z
    have hx'y' := h x' y' z
    apply mul_right_cancel₀ (ne_of_gt (mul_pos hz hz))
    calc
      p x y z * p x' y' z * (zMarginal p z * zMarginal p z) =
          (p x y z * zMarginal p z) * (p x' y' z * zMarginal p z) := by ring
      _ = ((∑ y', p x y' z) * (∑ x', p x' y z)) *
          ((∑ y', p x' y' z) * (∑ x', p x' y' z)) := by rw [hxy, hx'y']
      _ = ((∑ y', p x y' z) * (∑ x', p x' y' z)) *
          ((∑ y', p x' y' z) * (∑ x', p x' y z)) := by ring
      _ = (p x y' z * zMarginal p z) * (p x' y z * zMarginal p z) := by
        rw [hxy', hx'y]
      _ = p x y' z * p x' y z * (zMarginal p z * zMarginal p z) := by ring
  · intro h x y z
    have hs := congrArg (fun f : X → ℝ => ∑ x', f x')
      (funext (fun x' => congrArg (fun f : Y → ℝ => ∑ y', f y')
        (funext (fun y' => h x x' y y' z))))
    simp only [zMarginal]
    simp only [Finset.sum_mul, Finset.mul_sum] at hs ⊢
    exact hs

omit [Fintype Z] in
/-- Exact finite CI biconditional under positive separable selection, before the
irrelevant global normalization is applied. -/
theorem separable_selection_condIndep_iff
    (p : X → Y → Z → ℝ) (a : X → ℝ) (b : Y → ℝ) (c : Z → ℝ)
    (hp : ∀ x y z, 0 < p x y z)
    (ha : ∀ x, 0 < a x) (hb : ∀ y, 0 < b y) (hc : ∀ z, 0 < c z) :
    CondIndepMass (selectedMass p a b c) ↔ CondIndepMass p := by
  have hspos : ∀ x y z, 0 < selectedMass p a b c x y z := by
    intro x y z
    unfold selectedMass
    exact mul_pos (mul_pos (mul_pos (hp x y z) (ha x)) (hb y)) (hc z)
  rw [condIndepMass_iff_fourPoint (selectedMass p a b c) hspos]
  rw [condIndepMass_iff_fourPoint p hp]
  exact separable_selection_ci_iff p a b c ha hb hc

/-- **Finite normalized separable-selection CI bridge (stated statement).**

For a strictly positive normalized finite mass `p` and strictly positive
coordinate-separable selection weights, conditional independence for the
normalized selected mass is equivalent to conditional independence for the
original normalized mass.  The normalization hypothesis is retained exactly as
in the written statement, although the underlying CI equivalence is scale-invariant. -/
theorem normalized_separable_selection_condIndep_iff
    (p : X → Y → Z → ℝ) (a : X → ℝ) (b : Y → ℝ) (c : Z → ℝ)
    (hp : ∀ x y z, 0 < p x y z)
    (hp_norm : totalMass p = 1)
    (ha : ∀ x, 0 < a x) (hb : ∀ y, 0 < b y) (hc : ∀ z, 0 < c z) :
    CondIndepMass (normalizedSelectedMass p a b c) ↔
      CondIndepMass (normalizedMass p) := by
  have hn : totalMass p ≠ 0 := by rw [hp_norm]; norm_num
  have htypes : Nonempty X ∧ Nonempty Y ∧ Nonempty Z := by
    constructor
    · by_contra h
      rw [not_nonempty_iff] at h
      simp [totalMass] at hn
    constructor
    · by_contra h
      rw [not_nonempty_iff] at h
      simp [totalMass] at hn
    · by_contra h
      rw [not_nonempty_iff] at h
      simp [totalMass] at hn
  letI : Nonempty X := htypes.1
  letI : Nonempty Y := htypes.2.1
  letI : Nonempty Z := htypes.2.2
  have hspos : ∀ x y z, 0 < selectedMass p a b c x y z := by
    intro x y z
    unfold selectedMass
    exact mul_pos (mul_pos (mul_pos (hp x y z) (ha x)) (hb y)) (hc z)
  have hnormpos : 0 < selectedNormalizer p a b c := by
    simp only [selectedNormalizer, totalMass]
    exact Finset.sum_pos
      (fun x _ => Finset.sum_pos
        (fun y _ => Finset.sum_pos (fun z _ => hspos x y z) Finset.univ_nonempty)
        Finset.univ_nonempty)
      Finset.univ_nonempty
  have hsel : normalizedSelectedMass p a b c =
      selectedMass p (fun x => a x / selectedNormalizer p a b c) b c := by
    funext x y z
    simp only [normalizedSelectedMass, selectedMass]
    field_simp
  have hp_eq : normalizedMass p = p := by
    funext x y z
    simp [normalizedMass, hp_norm]
  rw [hsel, hp_eq]
  exact separable_selection_condIndep_iff p
    (fun x => a x / selectedNormalizer p a b c) b c hp
    (fun x => div_pos (ha x) hnormpos) hb hc

#print axioms condIndepMass_iff_fourPoint
#print axioms separable_selection_condIndep_iff
#print axioms normalized_separable_selection_condIndep_iff

end FiniteCI
end RecoveryFormal
