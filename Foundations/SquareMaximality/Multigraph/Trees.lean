import SquareMaximality.Multigraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Spanning trees of an edge-labelled multigraph

Mathlib's multigraph `Graph` API does not yet provide walks, cycles, or
spanning trees.  For a finite multigraph, the following standard
characterization is exact and avoids inventing a second walk theory:

* all selected labels are nonloops;
* their underlying simple graph is connected; and
* the number of selected labels is one less than the number of vertices.

Counting labels (rather than unordered endpoint pairs) is important: it
correctly treats two parallel selected edges as two edges.
-/

set_option autoImplicit false

namespace SquareMaximality.Multigraph
namespace LabeledMultigraph

variable {V E : Type*} (G : LabeledMultigraph V E)

/-- The simple graph supported by a specified set of edge labels.

This is used only to express connectivity.  The cardinality condition in
`IsSpanningTree` continues to count the original labels, including parallel
ones. -/
def simpleGraphOn (F : Set E) : SimpleGraph V where
  Adj u v := u ≠ v ∧ ∃ e ∈ F, G.IsLink e u v
  symm := {
    symm := fun u v h ↦
      ⟨h.1.symm, h.2.imp fun e he ↦ ⟨he.1, (G.isLink_comm e u v).mp he.2⟩⟩
  }
  loopless := {
    irrefl := fun _ h ↦ h.1 rfl
  }

@[simp]
theorem simpleGraphOn_adj (F : Set E) (u v : V) :
    (G.simpleGraphOn F).Adj u v ↔ u ≠ v ∧ ∃ e ∈ F, G.IsLink e u v :=
  Iff.rfl

theorem simpleGraphOn_mono {F F' : Set E} (hFF' : F ⊆ F') :
    G.simpleGraphOn F ≤ G.simpleGraphOn F' := by
  intro u v h
  exact ⟨h.1, h.2.imp fun e he ↦ ⟨hFF' he.1, he.2⟩⟩

@[simp]
theorem simpleGraphOn_univ : G.simpleGraphOn Set.univ = G.toSimpleGraph := by
  ext u v
  simp only [simpleGraphOn_adj, Set.mem_univ, true_and, toSimpleGraph_adj]

/-- A finite set of labelled edges is a spanning tree.

The equation `F.card + 1 = Fintype.card V` deliberately counts edge labels,
not edges of the underlying simple graph. -/
def IsSpanningTree [Fintype V] (F : Finset E) : Prop :=
  (∀ e ∈ F, ¬G.IsLoop e) ∧
    (G.simpleGraphOn (F : Set E)).Connected ∧
    F.card + 1 = Fintype.card V

namespace IsSpanningTree

variable [Fintype V] {G : LabeledMultigraph V E} {F : Finset E}

theorem loopless (hF : G.IsSpanningTree F) {e : E} (he : e ∈ F) : ¬G.IsLoop e :=
  hF.1 e he

theorem selected_connected (hF : G.IsSpanningTree F) :
    (G.simpleGraphOn (F : Set E)).Connected :=
  hF.2.1

theorem card_edges_add_one (hF : G.IsSpanningTree F) :
    F.card + 1 = Fintype.card V :=
  hF.2.2

theorem vertex_nonempty (hF : G.IsSpanningTree F) : Nonempty V := by
  rw [← Fintype.card_pos_iff]
  have hcard := hF.card_edges_add_one
  omega

theorem ambient_connected (hF : G.IsSpanningTree F) : G.Connected := by
  rw [Connected, ← simpleGraphOn_univ]
  exact hF.selected_connected.mono (G.simpleGraphOn_mono (Set.subset_univ _))

end IsSpanningTree

/-- The finite type of spanning labelled-edge sets. -/
abbrev SpanningTree [Fintype V] [Finite E] :=
  {F : Finset E // G.IsSpanningTree F}

section LoopDeletion

noncomputable local instance treeDecidableEqVertex : DecidableEq V := Classical.decEq V
noncomputable local instance treeDecidableNonLoop : DecidablePred (fun e : E ↦ ¬G.IsLoop e) :=
  Classical.decPred _

/-- Forget the subtype proof on a finite set of nonloop edge labels. -/
def forgetNonLoopEdges (F : Finset G.NonLoopEdge) : Finset E :=
  F.map (Function.Embedding.subtype _)

/-- Attach nonloop proofs to every eligible member of a finite edge set. -/
noncomputable def attachNonLoopEdges (F : Finset E) : Finset G.NonLoopEdge :=
  F.subtype fun e ↦ ¬G.IsLoop e

theorem forget_attachNonLoopEdges {F : Finset E} (hF : ∀ e ∈ F, ¬G.IsLoop e) :
    G.forgetNonLoopEdges (G.attachNonLoopEdges F) = F := by
  classical
  simpa [forgetNonLoopEdges, attachNonLoopEdges] using Finset.subtype_map_of_mem hF

@[simp]
theorem attach_forgetNonLoopEdges (F : Finset G.NonLoopEdge) :
    G.attachNonLoopEdges (G.forgetNonLoopEdges F) = F := by
  classical
  ext e
  simp [attachNonLoopEdges, forgetNonLoopEdges, e.2]

theorem simpleGraphOn_forgetNonLoopEdges (F : Finset G.NonLoopEdge) :
    G.simpleGraphOn (G.forgetNonLoopEdges F : Set E) =
      G.deleteLoops.simpleGraphOn (F : Set G.NonLoopEdge) := by
  classical
  ext u v
  simp [forgetNonLoopEdges]

theorem simpleGraphOn_attachNonLoopEdges {F : Finset E}
    (hF : ∀ e ∈ F, ¬G.IsLoop e) :
    G.deleteLoops.simpleGraphOn (G.attachNonLoopEdges F : Set G.NonLoopEdge) =
      G.simpleGraphOn (F : Set E) := by
  rw [← G.simpleGraphOn_forgetNonLoopEdges (G.attachNonLoopEdges F),
    G.forget_attachNonLoopEdges hF]

variable [Fintype V] [Finite E]

/-- Regard a spanning tree of the loop-deleted graph as a spanning tree of
the original graph. -/
def forgetSpanningTree (T : G.deleteLoops.SpanningTree) : G.SpanningTree := by
  refine ⟨G.forgetNonLoopEdges T.1, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · intro e he
    obtain ⟨e', he', rfl⟩ := Finset.mem_map.mp he
    exact e'.2
  · rw [G.simpleGraphOn_forgetNonLoopEdges]
    exact T.2.selected_connected
  · simpa [forgetNonLoopEdges] using T.2.card_edges_add_one

/-- Regard a spanning tree of the original graph as a spanning tree after
loop deletion. -/
noncomputable def attachSpanningTree (T : G.SpanningTree) :
    G.deleteLoops.SpanningTree := by
  have hloop : ∀ e ∈ T.1, ¬G.IsLoop e := fun _ he ↦ T.2.loopless he
  refine ⟨G.attachNonLoopEdges T.1, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · intro e _
    exact e.2
  · rw [G.simpleGraphOn_attachNonLoopEdges hloop]
    exact T.2.selected_connected
  · simpa [attachNonLoopEdges, Finset.filter_eq_self.2 hloop] using
      T.2.card_edges_add_one

/-- Deleting loops gives an explicit equivalence of labelled spanning-tree
edge sets. -/
noncomputable def spanningTreeDeleteLoopsEquiv :
    G.deleteLoops.SpanningTree ≃ G.SpanningTree where
  toFun := G.forgetSpanningTree
  invFun := G.attachSpanningTree
  left_inv T := Subtype.ext (G.attach_forgetNonLoopEdges T.1)
  right_inv T := Subtype.ext (G.forget_attachNonLoopEdges fun _ he ↦ T.2.loopless he)

end LoopDeletion

/-- Number of spanning trees, with parallel choices counted separately and
loops excluded by `IsSpanningTree`. -/
noncomputable def spanningTreeCount [Fintype V] [Finite E] : ℕ :=
  Nat.card G.SpanningTree

@[simp]
theorem deleteLoops_spanningTreeCount [Fintype V] [Finite E] :
    G.deleteLoops.spanningTreeCount = G.spanningTreeCount := by
  classical
  unfold spanningTreeCount
  exact Nat.card_congr G.spanningTreeDeleteLoopsEquiv

theorem spanningTreeCount_pos_iff [Fintype V] [Finite E] :
    0 < G.spanningTreeCount ↔ ∃ F : Finset E, G.IsSpanningTree F := by
  letI := Fintype.ofFinite E
  rw [spanningTreeCount, Finite.card_pos_iff]
  exact nonempty_subtype

theorem spanningTreeCount_eq_zero_of_not_connected [Fintype V] [Finite E]
    (hG : ¬G.Connected) : G.spanningTreeCount = 0 := by
  letI := Fintype.ofFinite E
  by_contra hne
  have hpos : 0 < G.spanningTreeCount := Nat.pos_of_ne_zero hne
  obtain ⟨F, hF⟩ := G.spanningTreeCount_pos_iff.mp hpos
  exact hG hF.ambient_connected

end LabeledMultigraph
end SquareMaximality.Multigraph
