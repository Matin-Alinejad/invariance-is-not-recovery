import Mathlib

open scoped BigOperators

/-!
# query budget — Exact bounded-depth CI-query budget

This file formalises worst-case finite cardinality bounds for two conditional
independence (CI) query search strategies used in constraint-based causal
discovery, with the search space explicitly represented as
`(candidate, conditioningSet)` pairs.

* **Target bounded-separator search.**  For a fixed target variable `t` among
  `p` variables, the algorithm inspects, for every candidate variable `c ≠ t`,
  every conditioning set `S ⊆ V \ {t, c}` of size at most the depth `d`.  The
  search space is the set of pairs `(c, S)`.
* **Exhaustive two-sided global search.**  The algorithm inspects, for every
  *ordered* pair of distinct variables `(a, b)`, every conditioning set
  `S ⊆ V \ {a, b}` of size at most `d`.  The search space is the set of pairs
  `((a, b), S)`.

The `p` variables are represented by `Fin p`.

## Refactor note

The starter file wrote the finite sums with the deprecated `∑ l in s, _`
notation, which no longer parses in the pinned Mathlib.  The two budget
definitions below are the *same* mathematical quantities, rewritten with the
current `∑ l ∈ s, _` notation.  This is the only change to the pre-existing
definitions and it is a purely notational (definitionally identical) refactor.
-/

namespace RecoveryFormal

/-- Coarse target-query budget through depth `d`:
`(p-1)` candidates times the number of conditioning sets of size `≤ d` drawn
from a `(p-2)`-element ground set. -/
def targetQueryBudget (p d : ℕ) : ℕ :=
  (p - 1) * ∑ l ∈ Finset.range (d + 1), Nat.choose (p - 2) l

/-- Coarse two-sided global-query budget through depth `d`:
`2 * C(p,2)` ordered pairs times the number of conditioning sets of size `≤ d`
drawn from a `(p-2)`-element ground set. -/
def globalQueryBudget (p d : ℕ) : ℕ :=
  2 * Nat.choose p 2 * ∑ l ∈ Finset.range (d + 1), Nat.choose (p - 2) l

/-! ## Building blocks -/

/-- Conditioning sets: subsets of a `ground` set whose cardinality is at most
the depth `d`. -/
def condSets {p : ℕ} (ground : Finset (Fin p)) (d : ℕ) : Finset (Finset (Fin p)) :=
  ground.powerset.filter (fun S => S.card ≤ d)

/-- The number of conditioning sets of depth `≤ d` over a ground set is exactly
`∑_{l=0}^{d} C(|ground|, l)`. -/
theorem card_condSets {p : ℕ} (ground : Finset (Fin p)) (d : ℕ) :
    (condSets ground d).card = ∑ l ∈ Finset.range (d + 1), Nat.choose ground.card l := by
  unfold condSets
  have hbi : ground.powerset.filter (fun S => S.card ≤ d)
      = (Finset.range (d + 1)).biUnion (fun l => ground.powersetCard l) := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_biUnion, Finset.mem_range,
      Finset.mem_powersetCard]
    constructor
    · rintro ⟨hsub, hcard⟩; exact ⟨S.card, by omega, hsub, rfl⟩
    · rintro ⟨l, hl, hsub, hcard⟩; exact ⟨hsub, by omega⟩
  rw [hbi, Finset.card_biUnion]
  · exact Finset.sum_congr rfl (fun l _ => Finset.card_powersetCard l ground)
  · intro x _ y _ hxy
    apply Finset.disjoint_left.2
    intro S hSx hSy
    simp only [Finset.mem_powersetCard] at hSx hSy
    exact hxy (hSx.2 ▸ hSy.2)

/-- The candidate variables for a fixed target `t`: every variable other than
`t`. -/
def candidates (p : ℕ) (t : Fin p) : Finset (Fin p) :=
  Finset.univ.filter (fun x => x ≠ t)

/-- There are exactly `p - 1` candidates. -/
theorem card_candidates (p : ℕ) (t : Fin p) : (candidates p t).card = p - 1 := by
  unfold candidates
  rw [Finset.filter_ne']
  simp

/-- Removing two distinct variables from `Fin p` leaves a `(p-2)`-element ground
set. -/
theorem ground_card {p : ℕ} {t c : Fin p} (h : t ≠ c) :
    ((Finset.univ : Finset (Fin p)) \ {t, c}).card = p - 2 := by
  rw [Finset.card_sdiff]
  have hpair : ({t, c} : Finset (Fin p)).card = 2 := Finset.card_pair h
  simp [hpair]

/-! ## Target bounded-separator search space -/

/-- The finite search space of the target bounded-separator search: all pairs
`(c, S)` with candidate `c ≠ t` and conditioning set `S ⊆ V \ {t, c}` of size
`≤ d`. -/
def targetSearchSpace (p d : ℕ) (t : Fin p) : Finset (Fin p × Finset (Fin p)) :=
  (candidates p t).biUnion
    (fun c => (condSets (Finset.univ \ {t, c}) d).image (fun S => (c, S)))

/-- Exact cardinality of the target search space equals the target query
budget. -/
theorem card_targetSearchSpace (p d : ℕ) (t : Fin p) :
    (targetSearchSpace p d t).card = targetQueryBudget p d := by
  unfold targetSearchSpace
  rw [Finset.card_biUnion]
  · have hterm : ∀ c ∈ candidates p t,
        ((condSets (Finset.univ \ {t, c}) d).image (fun S => (c, S))).card
          = ∑ l ∈ Finset.range (d + 1), Nat.choose (p - 2) l := by
      intro c hc
      rw [Finset.card_image_of_injective _ (by intro a b hab; simpa using hab), card_condSets]
      have hne : t ≠ c := by
        simp only [candidates, Finset.mem_filter] at hc
        exact (Ne.symm hc.2)
      rw [ground_card hne]
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, card_candidates, smul_eq_mul]
    rfl
  · intro a ha b hb hab
    apply Finset.disjoint_left.2
    rintro x hxa hxb
    simp only [Finset.mem_image] at hxa hxb
    obtain ⟨Sa, _, rfl⟩ := hxa
    obtain ⟨Sb, _, hb2⟩ := hxb
    exact hab (congrArg Prod.fst hb2).symm

/-- Worst-case bound (as required by the stated result): the target search space
has cardinality at most the target query budget. -/
theorem card_targetSearchSpace_le (p d : ℕ) (t : Fin p) :
    (targetSearchSpace p d t).card ≤ targetQueryBudget p d :=
  (card_targetSearchSpace p d t).le

/-! ## Exhaustive two-sided global search space -/

/-- Ordered pairs of distinct variables. -/
def orderedPairs (p : ℕ) : Finset (Fin p × Fin p) :=
  (Finset.univ : Finset (Fin p)).offDiag

/-- There are exactly `p * (p - 1) = 2 * C(p, 2)` ordered pairs of distinct
variables. -/
theorem card_orderedPairs (p : ℕ) : (orderedPairs p).card = 2 * Nat.choose p 2 := by
  unfold orderedPairs
  rw [Finset.offDiag_card]
  simp only [Finset.card_univ, Fintype.card_fin]
  rw [Nat.choose_two_right]
  have h : 2 ∣ p * (p - 1) := (Nat.even_mul_pred_self p).two_dvd
  have he : p * (p - 1) = p * p - p := by rw [Nat.mul_sub, Nat.mul_one]
  omega

/-- The finite search space of the exhaustive two-sided global search: all pairs
`((a, b), S)` with `a ≠ b` and conditioning set `S ⊆ V \ {a, b}` of size `≤ d`. -/
def globalSearchSpace (p d : ℕ) : Finset ((Fin p × Fin p) × Finset (Fin p)) :=
  (orderedPairs p).biUnion
    (fun ab => (condSets (Finset.univ \ {ab.1, ab.2}) d).image (fun S => (ab, S)))

/-- Exact cardinality of the global search space equals the global query
budget. -/
theorem card_globalSearchSpace (p d : ℕ) :
    (globalSearchSpace p d).card = globalQueryBudget p d := by
  unfold globalSearchSpace
  rw [Finset.card_biUnion]
  · have hterm : ∀ ab ∈ orderedPairs p,
        ((condSets (Finset.univ \ {ab.1, ab.2}) d).image (fun S => (ab, S))).card
          = ∑ l ∈ Finset.range (d + 1), Nat.choose (p - 2) l := by
      intro ab hab
      rw [Finset.card_image_of_injective _ (by intro a b hab; simpa using hab), card_condSets]
      have hne : ab.1 ≠ ab.2 := by
        simp only [orderedPairs, Finset.mem_offDiag] at hab
        exact hab.2.2
      rw [ground_card hne]
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, card_orderedPairs, smul_eq_mul]
    rfl
  · intro a ha b hb hab
    apply Finset.disjoint_left.2
    rintro x hxa hxb
    simp only [Finset.mem_image] at hxa hxb
    obtain ⟨Sa, _, rfl⟩ := hxa
    obtain ⟨Sb, _, hb2⟩ := hxb
    exact hab (congrArg Prod.fst hb2).symm

/-- Worst-case bound (as required by the stated result): the global search space has
cardinality at most the global query budget. -/
theorem card_globalSearchSpace_le (p d : ℕ) :
    (globalSearchSpace p d).card ≤ globalQueryBudget p d :=
  (card_globalSearchSpace p d).le

end RecoveryFormal
