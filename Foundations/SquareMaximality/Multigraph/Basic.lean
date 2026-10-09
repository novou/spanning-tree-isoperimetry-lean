import Mathlib.Combinatorics.Graph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Finite edge-labelled multigraphs

The new `Graph` API in Mathlib deliberately represents the vertex and edge
sets inside ambient types.  The planar dual in `general.tex` instead has fixed
finite vertex and edge types, and every edge label has exactly two (unordered)
ends.  `LabeledMultigraph` is the small wrapper needed for that use case.

Parallel edges are retained because the endpoint function need not be
injective.  Loops are retained because its value may be a diagonal unordered
pair.  Finiteness is supplied by `Fintype` instances at the declarations that
need it.
-/

set_option autoImplicit false

namespace SquareMaximality.Multigraph

/-- An undirected multigraph whose edge labels are the elements of `E`.

No simplicity condition is imposed on `ends`: distinct labels can have the
same ends, and `ends e` can be diagonal. -/
structure LabeledMultigraph (V E : Type*) where
  ends : E → Sym2 V

namespace LabeledMultigraph

variable {V E : Type*} (G : LabeledMultigraph V E)
variable {e : E} {u v : V}

/-- Edge `e` has the unordered pair of ends `u`, `v`. -/
def IsLink (e : E) (u v : V) : Prop := G.ends e = s(u, v)

@[simp]
theorem isLink_comm (e : E) (u v : V) : G.IsLink e u v ↔ G.IsLink e v u := by
  simp only [IsLink]
  rw [Sym2.eq_swap]

/-- Edge `e` is a loop based at `v`. -/
def IsLoopAt (e : E) (v : V) : Prop := G.IsLink e v v

/-- Edge `e` is a loop (its unordered pair of ends is diagonal). -/
def IsLoop (e : E) : Prop := (G.ends e).IsDiag

theorem isLoop_iff_exists_isLoopAt (e : E) : G.IsLoop e ↔ ∃ v, G.IsLoopAt e v := by
  constructor
  · intro h
    refine ⟨(G.ends e).diagElem h, ?_⟩
    change G.ends e = s((G.ends e).diagElem h, (G.ends e).diagElem h)
    simpa [Sym2.diag] using (Sym2.diag_diagElem h).symm
  · rintro ⟨v, hv⟩
    change (G.ends e).IsDiag
    change G.ends e = s(v, v) at hv
    rw [hv]
    exact Sym2.diag_isDiag v

theorem not_isLoop_of_isLink_of_ne (h : G.IsLink e u v) (hne : u ≠ v) : ¬G.IsLoop e := by
  change G.ends e = s(u, v) at h
  change ¬(G.ends e).IsDiag
  rw [h, Sym2.mk_isDiag_iff]
  exact hne

/-- The edge type obtained by discarding all loop labels. -/
abbrev NonLoopEdge := {e : E // ¬G.IsLoop e}

/-- Delete all loops while retaining the original labels as a subtype.

The change of edge type makes it impossible to accidentally use a deleted
loop in a later edge set. -/
def deleteLoops : LabeledMultigraph V G.NonLoopEdge where
  ends e := G.ends e.1

@[simp]
theorem deleteLoops_ends (e : G.NonLoopEdge) : G.deleteLoops.ends e = G.ends e.1 :=
  rfl

@[simp]
theorem deleteLoops_isLink (e : G.NonLoopEdge) (u v : V) :
    G.deleteLoops.IsLink e u v ↔ G.IsLink e.1 u v :=
  Iff.rfl

theorem deleteLoops_loopless (e : G.NonLoopEdge) : ¬G.deleteLoops.IsLoop e := by
  exact e.2

/-- The corresponding Mathlib multigraph, with all elements of `V` and `E`
present as vertices and edges. -/
def toGraph : Graph V E where
  vertexSet := Set.univ
  edgeSet := Set.univ
  IsLink e u v := G.IsLink e u v
  isLink_symm _ _ := {
    symm := fun u v h ↦ (G.isLink_comm _ u v).mp h
  }
  eq_or_eq_of_isLink_of_isLink := by
    intro e u v x y huv hxy
    have hpair : s(u, v) = s(x, y) := by
      rw [← huv, ← hxy]
    exact (Sym2.eq_iff.mp hpair).elim (fun h ↦ Or.inl h.1) (fun h ↦ Or.inr h.1)
  edge_mem_iff_exists_isLink := by
    intro e
    constructor
    · intro _
      induction hends : G.ends e using Sym2.inductionOn with
      | _ u v => exact ⟨u, v, hends⟩
    · intro _
      exact Set.mem_univ e
  left_mem_of_isLink := by
    intro _ _ _ _
    exact Set.mem_univ _

@[simp]
theorem toGraph_vertexSet : G.toGraph.vertexSet = Set.univ :=
  rfl

@[simp]
theorem toGraph_edgeSet : G.toGraph.edgeSet = Set.univ :=
  rfl

@[simp]
theorem toGraph_isLink (e : E) (u v : V) : G.toGraph.IsLink e u v ↔ G.IsLink e u v :=
  Iff.rfl

@[simp]
theorem toGraph_adj (u v : V) : G.toGraph.Adj u v ↔ ∃ e, G.IsLink e u v :=
  Iff.rfl

/-- The underlying simple graph.  Parallel labels are merged and loops are
discarded. -/
def toSimpleGraph : SimpleGraph V where
  Adj u v := u ≠ v ∧ ∃ e, G.IsLink e u v
  symm := {
    symm := fun u v h ↦
      ⟨h.1.symm, h.2.imp fun e he ↦ (G.isLink_comm e u v).mp he⟩
  }
  loopless := {
    irrefl := fun _ h ↦ h.1 rfl
  }

@[simp]
theorem toSimpleGraph_adj (u v : V) :
    G.toSimpleGraph.Adj u v ↔ u ≠ v ∧ ∃ e, G.IsLink e u v :=
  Iff.rfl

theorem toSimpleGraph_adj_iff_toGraph_adj (u v : V) :
    G.toSimpleGraph.Adj u v ↔ u ≠ v ∧ G.toGraph.Adj u v := by
  rfl

/-- Loop deletion does not change the underlying simple graph. -/
@[simp]
theorem deleteLoops_toSimpleGraph : G.deleteLoops.toSimpleGraph = G.toSimpleGraph := by
  ext u v
  constructor
  · rintro ⟨hne, e, he⟩
    exact ⟨hne, e.1, he⟩
  · rintro ⟨hne, e, he⟩
    exact ⟨hne, ⟨e, G.not_isLoop_of_isLink_of_ne he hne⟩, he⟩

/-- Connectivity for an edge-labelled multigraph is connectivity after
forgetting labels and loops. -/
def Connected : Prop := G.toSimpleGraph.Connected

theorem connected_iff_toSimpleGraph_connected :
    G.Connected ↔ G.toSimpleGraph.Connected :=
  Iff.rfl

@[simp]
theorem deleteLoops_connected : G.deleteLoops.Connected ↔ G.Connected := by
  rw [Connected, Connected, deleteLoops_toSimpleGraph]

end LabeledMultigraph

end SquareMaximality.Multigraph
