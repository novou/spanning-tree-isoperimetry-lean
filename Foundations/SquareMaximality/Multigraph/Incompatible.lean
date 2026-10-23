module

public import SquareMaximality.Multigraph.Events
public import Mathlib.Algebra.BigOperators.Field

@[expose] public section

/-!
# Incompatible spanning-tree containment events

The interior-vacancy argument in `general.tex` sums containment probabilities
over a family of mutually incompatible forests.  This file proves that step
directly by finite counting.  It does not use determinants, Matrix--Tree, or
probability theory.
-/

set_option autoImplicit false

namespace SquareMaximality.Multigraph
namespace LabeledMultigraph

variable {V E ι : Type*} (G : LabeledMultigraph V E)
variable [Fintype V] [Fintype E] [Fintype ι]

noncomputable local instance incompatibleDecidableEqEdge : DecidableEq E := Classical.decEq E

/-- Edge-containment events indexed by `ι` are incompatible when no ambient
spanning tree contains two distinct blocks. -/
def PairwiseIncompatible (F : ι → Finset E) : Prop :=
  Pairwise fun i j => ¬G.IsEdgeForest (F i ∪ F j)

omit [Fintype ι] in
theorem pairwiseDisjoint_spanningTreesContaining
    {F : ι → Finset E} (hF : G.PairwiseIncompatible F) :
    Set.PairwiseDisjoint Set.univ (G.spanningTreesContaining ∘ F) := by
  intro i _ j _ hij
  change Disjoint (G.spanningTreesContaining (F i))
    (G.spanningTreesContaining (F j))
  rw [Finset.disjoint_left]
  intro T hi hj
  apply hF hij
  refine ⟨T, ?_⟩
  intro e he
  rcases Finset.mem_union.mp he with hei | hej
  · exact (Finset.mem_filter.mp hi).2 hei
  · exact (Finset.mem_filter.mp hj).2 hej

/-- The total number of trees in pairwise incompatible containment events is
at most the total number of ambient spanning trees. -/
theorem sum_containmentCount_le
    {F : ι → Finset E} (hF : G.PairwiseIncompatible F) :
    ∑ i, G.containmentCount (F i) ≤ G.spanningTreeCount := by
  classical
  let events : ι → Finset G.SpanningTree := G.spanningTreesContaining ∘ F
  have hdisj : Set.PairwiseDisjoint (↑(Finset.univ : Finset ι) : Set ι) events := by
    simpa [events] using G.pairwiseDisjoint_spanningTreesContaining hF
  calc
    ∑ i, G.containmentCount (F i) =
        ((Finset.univ : Finset ι).biUnion events).card := by
      rw [Finset.card_biUnion hdisj]
      simp [events, containmentCount]
    _ ≤ G.spanningTrees.card := by
      apply Finset.card_le_card
      intro T hT
      rcases Finset.mem_biUnion.mp hT with ⟨i, _, hi⟩
      exact (Finset.mem_filter.mp hi).1
    _ = G.spanningTreeCount := G.card_spanningTrees

/-- Under the uniform spanning-tree measure, probabilities of pairwise
incompatible containment events sum to at most one. -/
theorem sum_containmentRatio_le_one
    (hG : 0 < G.spanningTreeCount)
    {F : ι → Finset E} (hF : G.PairwiseIncompatible F) :
    ∑ i, G.containmentRatio (F i) ≤ 1 := by
  have hden : (0 : ℝ) < G.spanningTreeCount := by exact_mod_cast hG
  rw [show (∑ i, G.containmentRatio (F i)) =
      ((∑ i, G.containmentCount (F i) : ℕ) : ℝ) /
        (G.spanningTreeCount : ℝ) by
    simp only [containmentRatio, Nat.cast_sum]
    exact (Finset.sum_div _ _ _).symm]
  rw [div_le_one hden]
  exact_mod_cast G.sum_containmentCount_le hF

end LabeledMultigraph
end SquareMaximality.Multigraph
