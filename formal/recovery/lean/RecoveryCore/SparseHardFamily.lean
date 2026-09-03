import Mathlib

namespace RecoveryCore

/-- A combinatorial encoding for a disjoint-pair DAG family.
Each bit controls at most one edge inside one two-node block. -/
def pairEdgeCount (θ : Fin n → Bool) : ℕ :=
  Finset.univ.filter (fun i => θ i = true) |>.card

/-- Undirected adjacency of the disjoint-pair family on vertices `Fin (2*n)`:
vertices `2k` and `2k+1` are adjacent iff bit `k` is on. -/
def pairAdj (θ : Fin n → Bool) (u v : Fin (2 * n)) : Prop :=
  ∃ k : Fin n, θ k = true ∧
    ((u.val = 2 * k.val ∧ v.val = 2 * k.val + 1) ∨
     (u.val = 2 * k.val + 1 ∧ v.val = 2 * k.val))

/-- Every graph in the disjoint-pair family has maximum degree at most one: each vertex
has at most one neighbour (any two neighbours of a vertex coincide).

Modification note: the starter file stated this as the placeholder `… : True`, deferring the
graph representation.  The representation is now fixed as `pairAdj` (mirroring the pair-family
edge relation of `RecoveryFormal.pairEdge`), and the intended combinatorial content
("maximum degree ≤ 1") is stated and proved faithfully. -/
theorem pair_family_max_degree_le_one (θ : Fin n → Bool) :
    ∀ u v w : Fin (2 * n), pairAdj θ u v → pairAdj θ u w → v = w := by
  intro u v w hv hw
  obtain ⟨k, _, hk⟩ := hv
  obtain ⟨j, _, hj⟩ := hw
  apply Fin.ext
  rcases hk with ⟨hu1, hv1⟩ | ⟨hu1, hv1⟩ <;>
    rcases hj with ⟨hu2, hw2⟩ | ⟨hu2, hw2⟩ <;> omega

/-- Number of possible bit vectors in the disjoint-pair family. -/
theorem pair_family_cardinality : Fintype.card (Fin n → Bool) = 2 ^ n := by
  simp

end RecoveryCore
