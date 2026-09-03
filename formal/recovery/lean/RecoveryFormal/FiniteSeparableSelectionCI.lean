import Mathlib

namespace RecoveryFormal

/-- Four-point conditional-independence criterion at every conditioning value. -/
def FourPointCI {X Y Z : Type*}
    (p : X → Y → Z → ℝ) : Prop :=
  ∀ x x' y y' z,
    p x y z * p x' y' z = p x y' z * p x' y z

/-- Unnormalised coordinate-separable selected mass. -/
def selectedMass {X Y Z : Type*}
    (p : X → Y → Z → ℝ)
    (a : X → ℝ) (b : Y → ℝ) (c : Z → ℝ) : X → Y → Z → ℝ :=
  fun x y z => p x y z * a x * b y * c z

/-- Positive separable selection preserves and reflects the four-point CI identity.

For strictly positive coordinate-separable selection weights `a`, `b`, `c`, the
four-point conditional-independence criterion holds for the selected mass
`selectedMass p a b c` iff it holds for the original mass `p`.

The proof observes that each side of the selected four-point identity carries the
same strictly positive factor `a x * a x' * b y * b y' * (c z)^2`; the forward
direction cancels this positive factor (`mul_right_cancel₀`), and the reverse
direction reintroduces it (`linear_combination`). -/
theorem separable_selection_ci_iff
    {X Y Z : Type*}
    (p : X → Y → Z → ℝ)
    (a : X → ℝ) (b : Y → ℝ) (c : Z → ℝ)
    (ha : ∀ x, 0 < a x)
    (hb : ∀ y, 0 < b y)
    (hc : ∀ z, 0 < c z) :
    FourPointCI (selectedMass p a b c) ↔ FourPointCI p := by
  constructor
  · -- Reflection: CI after selection ⇒ CI before selection (cancel positive factor).
    intro h x x' y y' z
    have hfac : 0 < a x * a x' * b y * b y' * (c z * c z) := by
      have := ha x; have := ha x'; have := hb y; have := hb y'; have := hc z
      positivity
    have hthis := h x x' y y' z
    simp only [selectedMass] at hthis
    apply mul_right_cancel₀ (ne_of_gt hfac)
    linear_combination hthis
  · -- Preservation: CI before selection ⇒ CI after selection (reintroduce factor).
    intro h x x' y y' z
    simp only [selectedMass]
    have hthis := h x x' y y' z
    linear_combination (a x * a x' * b y * b y' * (c z * c z)) * hthis

#print axioms separable_selection_ci_iff

end RecoveryFormal
