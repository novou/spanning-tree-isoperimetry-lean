module

public import SquareMaximality.Main

@[expose] public section

set_option autoImplicit false

/-!
# Reduction to induced square-lattice graphs

This file checks the reduction in the introduction of `general.tex`.  A spanning tree of a
spanning subgraph is still a spanning tree after edges are added, so spanning-tree count is
monotone.  If the original graph is connected and at least one edge is genuinely new, the
inequality is strict: the new edge is an acyclic subgraph of the larger connected graph and
can therefore be extended to a spanning tree containing that edge.
-/

namespace SquareMaximality

open SimpleGraph

section TreeCountMonotonicity

universe u

variable {V : Type u} [Finite V]
variable {G H : SimpleGraph V}

/-- Adding edges to a finite graph cannot decrease its number of spanning trees. -/
theorem treeCount_mono (hGH : G ≤ H) : treeCount G ≤ treeCount H := by
  unfold treeCount
  let includeTrees :
      {T : SimpleGraph V // T ≤ G ∧ T.IsTree} →
        {T : SimpleGraph V // T ≤ H ∧ T.IsTree} :=
    fun T ↦ ⟨T.1, T.2.1.trans hGH, T.2.2⟩
  exact Nat.card_le_card_of_injective includeTrees fun T U hTU ↦ by
    apply Subtype.ext
    exact congrArg (fun X ↦ X.1) hTU

/-- Adding an edge to a connected finite graph strictly increases its spanning-tree count.

The two adjacency assumptions say that the edge `uv` belongs to `H` but not to `G`.
-/
theorem treeCount_lt_of_connected_of_added_edge
    (hG : G.Connected) (hGH : G ≤ H) {u v : V}
    (huvH : H.Adj u v) (huvG : ¬G.Adj u v) :
    treeCount G < treeCount H := by
  unfold treeCount
  apply Set.Finite.card_lt_card (Set.toFinite _)
  constructor
  · rintro T ⟨hTG, hT⟩
    exact ⟨hTG.trans hGH, hT⟩
  · intro hreverse
    have huv_ne : u ≠ v := huvH.ne
    have hedge_le : edge u v ≤ H := (edge_le_iff H).2 (Or.inr huvH)
    have hedge_acyclic : (edge u v).IsAcyclic := by
      have hnot_reachable : ¬(⊥ : SimpleGraph V).Reachable u v := by
        exact fun hreach ↦ huv_ne (reachable_bot.mp hreach)
      rw [← bot_sup_eq (edge u v)]
      exact isAcyclic_bot.sup_edge_of_not_reachable hnot_reachable
    have hH : H.Connected := hG.mono hGH
    obtain ⟨T, hedgeT, hTH, hT⟩ :=
      hH.exists_isTree_le_of_le_of_isAcyclic hedge_le hedge_acyclic
    have hT_in_H : T ∈ {T : SimpleGraph V | T ≤ H ∧ T.IsTree} := ⟨hTH, hT⟩
    have hT_in_G : T ∈ {T : SimpleGraph V | T ≤ G ∧ T.IsTree} := hreverse hT_in_H
    apply huvG
    apply hT_in_G.1
    apply hedgeT
    exact (edge_adj u v u v).2 ⟨Or.inl ⟨rfl, rfl⟩, huv_ne⟩

/-- A proper supergraph of a connected finite graph has strictly more spanning trees. -/
theorem treeCount_strictMono_of_connected (hG : G.Connected) (hGH : G < H) :
    treeCount G < treeCount H := by
  have hmissing : ∃ u v, H.Adj u v ∧ ¬G.Adj u v := by
    by_contra h
    apply hGH.2
    intro u v huvH
    by_contra huvG
    exact h ⟨u, v, huvH, huvG⟩
  obtain ⟨u, v, huvH, huvG⟩ := hmissing
  exact treeCount_lt_of_connected_of_added_edge hG hGH.le huvH huvG

end TreeCountMonotonicity

section InducedGridReduction

/-- Conditional square maximality for every spanning subgraph of the grid induced by `S`.

This is the precise formal counterpart of the introduction's reduction from an arbitrary
square-lattice graph with vertex set `S` to the induced graph on `S`.
-/
theorem spanningSubgraph_squareMaximality_of_inputs
    {κ : ℝ} (inputs : MaximalityInputs κ)
    {n : ℕ} (hn : 0 < n) (S : Finset Point) (hcard : S.card = n ^ 2)
    (G : SimpleGraph {p : Point // p ∈ S}) (hG : G ≤ inducedGrid S) :
    treeCount G ≤ tauRect n n := by
  calc
    treeCount G ≤ treeCount (inducedGrid S) := treeCount_mono hG
    _ = tau S := rfl
    _ ≤ tauRect n n := squareMaximality_of_inputs inputs hn S hcard

/-- Under the same conditional inputs, equality with the square is impossible for a proper
connected spanning subgraph of the induced grid. -/
theorem spanningSubgraph_lt_square_of_inputs
    {κ : ℝ} (inputs : MaximalityInputs κ)
    {n : ℕ} (hn : 0 < n) (S : Finset Point) (hcard : S.card = n ^ 2)
    (G : SimpleGraph {p : Point // p ∈ S}) (hconn : G.Connected)
    (hproper : G < inducedGrid S) :
    treeCount G < tauRect n n := by
  calc
    treeCount G < treeCount (inducedGrid S) :=
      treeCount_strictMono_of_connected hconn hproper
    _ = tau S := rfl
    _ ≤ tauRect n n := squareMaximality_of_inputs inputs hn S hcard

end InducedGridReduction

end SquareMaximality
