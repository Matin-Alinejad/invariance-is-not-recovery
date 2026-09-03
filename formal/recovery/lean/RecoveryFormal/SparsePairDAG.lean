import Mathlib

namespace RecoveryFormal

/-!
# Explicit sparse pair-DAG family

For a bit vector `θ : Fin m → Bool` we build a directed graph on the `2*m`
vertices `Fin (2*m)`.  For each block index `k : Fin m` there is a single
possible directed edge `2*k → 2*k+1`, and it is present exactly when `θ k = true`.

This file formalizes the structural properties of that family:

* every edge strictly increases the natural vertex index
  (`pairEdge_index_increases`);
* the directed graph is acyclic (`pairEdge_acyclic`);
* the undirected skeleton has maximum degree `≤ 1` (`pairAdj_degree_le_one`);
* the number of edges equals the Hamming weight of `θ`
  (`edgeFinset_card_eq_bitWeight`);
* the symmetric difference of the two skeletons of `θ` and `θ'` has cardinality
  equal to the bit Hamming distance of `θ` and `θ'`
  (`edgeFinset_symmDiff_card_eq_bitHamming`).
-/

/-- Pair-family directed edge relation on vertices `Fin (2*m)`. -/
def pairEdge {m : ℕ} (θ : Fin m → Bool)
    (u v : Fin (2 * m)) : Prop :=
  ∃ k : Fin m,
    θ k = true ∧ u.val = 2 * k.val ∧ v.val = 2 * k.val + 1

/-- Every pair-family edge points from a smaller to a larger natural index. -/
theorem pairEdge_index_increases {m : ℕ} (θ : Fin m → Bool)
    {u v : Fin (2 * m)} (h : pairEdge θ u v) : u.val < v.val := by
  obtain ⟨k, _, hu, hv⟩ := h
  omega

/-- The transitive closure of the edge relation also strictly increases the
natural vertex index. -/
theorem pairEdge_transGen_index_increases {m : ℕ} (θ : Fin m → Bool)
    {u v : Fin (2 * m)} (h : Relation.TransGen (pairEdge θ) u v) :
    u.val < v.val := by
  induction h with
  | single h => exact pairEdge_index_increases θ h
  | tail _ hbc ih => exact lt_trans ih (pairEdge_index_increases θ hbc)

/-- The pair-family directed graph is acyclic: no vertex reaches itself along a
nonempty directed path. -/
theorem pairEdge_acyclic {m : ℕ} (θ : Fin m → Bool) (u : Fin (2 * m)) :
    ¬ Relation.TransGen (pairEdge θ) u u := by
  intro h
  exact lt_irrefl _ (pairEdge_transGen_index_increases θ h)

/-- Undirected skeleton adjacency relation: `u` and `v` are adjacent when there
is a directed edge in either direction. -/
def pairAdj {m : ℕ} (θ : Fin m → Bool) (u v : Fin (2 * m)) : Prop :=
  pairEdge θ u v ∨ pairEdge θ v u

instance {m : ℕ} (θ : Fin m → Bool) (u v : Fin (2 * m)) :
    Decidable (pairEdge θ u v) := by
  unfold pairEdge; infer_instance

instance {m : ℕ} (θ : Fin m → Bool) (u v : Fin (2 * m)) :
    Decidable (pairAdj θ u v) := by
  unfold pairAdj; infer_instance

/-- The undirected skeleton has maximum degree at most one: every vertex has at
most one neighbour. -/
theorem pairAdj_degree_le_one {m : ℕ} (θ : Fin m → Bool) (u : Fin (2 * m)) :
    (Finset.univ.filter (fun v => pairAdj θ u v)).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro v hv w hw
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, pairAdj, pairEdge] at hv hw
  apply Fin.ext
  obtain (⟨k, _, hu, hv2⟩ | ⟨k, _, hv2, hu⟩) := hv <;>
    obtain (⟨l, _, hu2, hw2⟩ | ⟨l, _, hw2, hu2⟩) := hw <;> omega

/-- The two endpoints of the (possible) edge controlled by block `k`. -/
def edgeOf {m : ℕ} (k : Fin m) : Fin (2 * m) × Fin (2 * m) :=
  (⟨2 * k.val, by have := k.isLt; omega⟩,
   ⟨2 * k.val + 1, by have := k.isLt; omega⟩)

theorem edgeOf_injective {m : ℕ} : Function.Injective (edgeOf (m := m)) := by
  intro a b hab
  simp only [edgeOf, Prod.mk.injEq, Fin.mk.injEq] at hab
  exact Fin.ext (by omega)

/-- The finite set of directed edges present for the bit vector `θ`. -/
def edgeFinset {m : ℕ} (θ : Fin m → Bool) : Finset (Fin (2 * m) × Fin (2 * m)) :=
  (Finset.univ.filter (fun k => θ k = true)).image edgeOf

/-- Hamming weight of `θ`: the number of `true` bits. -/
def bitWeight {m : ℕ} (θ : Fin m → Bool) : ℕ :=
  (Finset.univ.filter (fun k => θ k = true)).card

/-- Bit Hamming distance between `θ` and `θ'`: number of positions where they
disagree. -/
def bitHamming {m : ℕ} (θ θ' : Fin m → Bool) : ℕ :=
  (Finset.univ.filter (fun k => θ k ≠ θ' k)).card

/-- Characterisation of `edgeFinset` membership. -/
theorem mem_edgeFinset {m : ℕ} (θ : Fin m → Bool)
    (p : Fin (2 * m) × Fin (2 * m)) :
    p ∈ edgeFinset θ ↔ ∃ k : Fin m, θ k = true ∧ p = edgeOf k := by
  simp only [edgeFinset, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨k, hk, rfl⟩; exact ⟨k, hk, rfl⟩
  · rintro ⟨k, hk, rfl⟩; exact ⟨k, hk, rfl⟩

/-- The number of edges equals the Hamming weight of `θ`. -/
theorem edgeFinset_card_eq_bitWeight {m : ℕ} (θ : Fin m → Bool) :
    (edgeFinset θ).card = bitWeight θ := by
  unfold edgeFinset bitWeight
  rw [Finset.card_image_of_injective _ edgeOf_injective]

/-- The symmetric difference of the two skeletons of `θ` and `θ'` has cardinality
equal to the bit Hamming distance of `θ` and `θ'`. -/
theorem edgeFinset_symmDiff_card_eq_bitHamming {m : ℕ} (θ θ' : Fin m → Bool) :
    (symmDiff (edgeFinset θ) (edgeFinset θ')).card = bitHamming θ θ' := by
  unfold edgeFinset bitHamming
  rw [← Finset.image_symmDiff _ _ edgeOf_injective,
    Finset.card_image_of_injective _ edgeOf_injective]
  congr 1
  ext k
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_symmDiff]
  cases hθ : θ k <;> cases hθ' : θ' k <;> simp

/-! ## Axiom audit for every exported theorem -/

#print axioms pairEdge_index_increases
#print axioms pairEdge_transGen_index_increases
#print axioms pairEdge_acyclic
#print axioms pairAdj_degree_le_one
#print axioms edgeOf_injective
#print axioms mem_edgeFinset
#print axioms edgeFinset_card_eq_bitWeight
#print axioms edgeFinset_symmDiff_card_eq_bitHamming

end RecoveryFormal
