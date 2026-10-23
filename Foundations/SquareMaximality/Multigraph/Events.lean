module

public import SquareMaximality.Multigraph.All
public import Mathlib.Data.Real.Basic

@[expose] public section

set_option autoImplicit false

/-!
# Uniform spanning-tree containment events

This file gives a finite counting formulation of the forest events used in
`general.tex`.  It also closes the manuscript's omitted zero-block endpoint:
the containment probability of the empty forest is one, and the empty product
is one.  The substantive transfer-current/Hadamard--Fischer inequality remains
a named proposition that a later matrix proof must establish.
-/

namespace SquareMaximality.Multigraph

namespace LabeledMultigraph

variable {V E : Type*} (G : LabeledMultigraph V E)
variable [Fintype V] [Fintype E]

/-- The finite set of all labelled spanning trees. -/
noncomputable def spanningTrees : Finset G.SpanningTree := by
  classical
  exact Finset.univ

/-- Spanning trees containing every label in `F`. -/
noncomputable def spanningTreesContaining (F : Finset E) : Finset G.SpanningTree := by
  classical
  exact G.spanningTrees.filter fun T => F ⊆ T.1

/-- The number of spanning trees containing `F`. -/
noncomputable def containmentCount (F : Finset E) : ℕ :=
  (G.spanningTreesContaining F).card

/-- The probability of containing `F` under the uniform spanning-tree measure.
It is defined as zero if the ambient graph has no spanning tree. -/
noncomputable def containmentRatio (F : Finset E) : ℝ :=
  (G.containmentCount F : ℝ) / (G.spanningTreeCount : ℝ)

@[simp] theorem card_spanningTrees : G.spanningTrees.card = G.spanningTreeCount := by
  classical
  simp [spanningTrees, spanningTreeCount, Nat.card_eq_fintype_card]

@[simp] theorem spanningTreesContaining_empty :
    G.spanningTreesContaining ∅ = G.spanningTrees := by
  classical
  simp [spanningTreesContaining]

@[simp] theorem containmentCount_empty :
    G.containmentCount ∅ = G.spanningTreeCount := by
  simp [containmentCount]

theorem containmentRatio_empty (hG : 0 < G.spanningTreeCount) :
    G.containmentRatio ∅ = 1 := by
  rw [containmentRatio, containmentCount_empty]
  apply div_self
  exact_mod_cast Nat.ne_of_gt hG

theorem containmentCount_mono {F F' : Finset E} (hFF' : F ⊆ F') :
    G.containmentCount F' ≤ G.containmentCount F := by
  classical
  apply Finset.card_le_card
  intro T hT
  simp only [spanningTreesContaining, Finset.mem_filter] at hT ⊢
  exact ⟨hT.1, hFF'.trans hT.2⟩

theorem containmentRatio_nonneg (F : Finset E) : 0 ≤ G.containmentRatio F := by
  apply div_nonneg <;> exact_mod_cast Nat.zero_le _

/-- A labelled edge set is a forest when it extends to a spanning tree of the
ambient graph.  This is the graphic-matroid independence formulation used by
the transfer-current theorem. -/
def IsEdgeForest (F : Finset E) : Prop :=
  ∃ T : G.SpanningTree, F ⊆ T.1

theorem isEdgeForest_mono {F F' : Finset E}
    (hF' : G.IsEdgeForest F') (hFF' : F ⊆ F') : G.IsEdgeForest F := by
  rcases hF' with ⟨T, hT⟩
  exact ⟨T, hFF'.trans hT⟩

theorem containmentCount_pos_of_isEdgeForest {F : Finset E}
    (hF : G.IsEdgeForest F) : 0 < G.containmentCount F := by
  classical
  rcases hF with ⟨T, hT⟩
  apply Finset.card_pos.mpr
  refine ⟨T, ?_⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hT⟩

theorem containmentRatio_pos_of_isEdgeForest
    (hG : 0 < G.spanningTreeCount) {F : Finset E}
    (hF : G.IsEdgeForest F) : 0 < G.containmentRatio F := by
  apply div_pos
  · exact_mod_cast G.containmentCount_pos_of_isEdgeForest hF
  · exact_mod_cast hG

/-- Union of a finite indexed family of edge blocks. -/
noncomputable def unionEdgeBlocks {ι : Type*} [Fintype ι]
    (F : ι → Finset E) : Finset E := by
  classical
  exact Finset.univ.biUnion F

omit [Fintype E] in
@[simp] theorem mem_unionEdgeBlocks {ι : Type*} [Fintype ι]
    {F : ι → Finset E} {e : E} :
    e ∈ unionEdgeBlocks F ↔ ∃ i, e ∈ F i := by
  classical
  simp [unionEdgeBlocks]

/-- The nonempty-family form of forest negative correlation stated in the
manuscript.  This is a proposition, not an axiom: its eventual proof is the
transfer-current/Hadamard--Fischer task. -/
def ForestBlockNegativeCorrelation : Prop :=
  ∀ (ι : Type) [Fintype ι] [Nonempty ι] (F : ι → Finset E),
    Pairwise (fun i j => Disjoint (F i) (F j)) →
    G.IsEdgeForest (unionEdgeBlocks F) →
    G.containmentRatio (unionEdgeBlocks F) ≤
      ∏ i, G.containmentRatio (F i)

/-- Forest negative correlation, including the zero-block case omitted in the
paper's invocation. -/
theorem forestBlockNegativeCorrelation_all
    (hG : 0 < G.spanningTreeCount)
    (hneg : G.ForestBlockNegativeCorrelation)
    {ι : Type} [Fintype ι] (F : ι → Finset E)
    (hdisj : Pairwise (fun i j => Disjoint (F i) (F j)))
    (hforest : G.IsEdgeForest (unionEdgeBlocks F)) :
    G.containmentRatio (unionEdgeBlocks F) ≤
      ∏ i, G.containmentRatio (F i) := by
  cases isEmpty_or_nonempty ι with
  | inl hempty =>
      letI := hempty
      have hunion : unionEdgeBlocks F = ∅ := by
        classical
        ext e
        simp
      simp [hunion, G.containmentRatio_empty hG]
  | inr hnonempty =>
      letI := hnonempty
      exact hneg ι F hdisj hforest

end LabeledMultigraph

end SquareMaximality.Multigraph
