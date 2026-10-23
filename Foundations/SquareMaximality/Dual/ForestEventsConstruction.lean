module

public import SquareMaximality.Dual.PlanarComplement
public import SquareMaximality.Dual.ForestProduct
public import SquareMaximality.Dual.InteriorTapp
public import SquareMaximality.Dual.RectangleTransferCurrent

@[expose] public section

set_option backward.privateInPublic true

/-!
# Constructing the canonical forest events from planar complements

The probability events use a forest of selected dual labels, whereas the
geometric deletion law naturally contracts every dual label incident with a
deleted primal vertex.  This file supplies the finite bridge between those
two presentations.  Its first part is completely graph theoretic: contracting
two label sets with the same reachability relation gives isomorphic labelled
multigraphs, including an explicit equivalence of their spanning-tree types.
-/

set_option autoImplicit false

namespace SquareMaximality
namespace Dual

open Multigraph
open Multigraph.LabeledMultigraph

noncomputable section

namespace ContractionRelabel

variable {V E : Type*} [Fintype V] [Fintype E]

/-- A simultaneous relabelling of the vertices and edge labels of a labelled
multigraph.  The endpoint equation is deliberately oriented toward mapping
objects from `G` to `H`. -/
structure Iso (G : LabeledMultigraph V E)
    {W D : Type*} [Fintype W] [Fintype D]
    (H : LabeledMultigraph W D) where
  vertexEquiv : V ≃ W
  edgeEquiv : E ≃ D
  map_ends : ∀ e, H.ends (edgeEquiv e) = Sym2.map vertexEquiv (G.ends e)

namespace Iso

variable {G : LabeledMultigraph V E}
variable {W D : Type*} [Fintype W] [Fintype D]
variable {H : LabeledMultigraph W D}

/-- Relabel a finite edge set. -/
def mapFinset (e : Iso G H) (F : Finset E) : Finset D :=
  F.map e.edgeEquiv.toEmbedding

omit [Fintype V] [Fintype E] in
@[simp] theorem mem_mapFinset (e : Iso G H) (F : Finset E) (d : D) :
    d ∈ e.mapFinset F ↔ e.edgeEquiv.symm d ∈ F := by
  classical
  simp [mapFinset]

omit [Fintype V] [Fintype E] in
@[simp] theorem mapFinset_card (e : Iso G H) (F : Finset E) :
    (e.mapFinset F).card = F.card := by
  classical
  exact Finset.card_map _

/-- The selected underlying simple graphs are isomorphic after relabelling. -/
def simpleGraphOnIso (e : Iso G H) (F : Finset E) :
    G.simpleGraphOn (F : Set E) ≃g
      H.simpleGraphOn (e.mapFinset F : Set D) where
  toEquiv := e.vertexEquiv
  map_rel_iff' := by
    intro u v
    constructor
    · rintro ⟨huv, d, hdF, hdlink⟩
      let a := e.edgeEquiv.symm d
      have haF : a ∈ F := (e.mem_mapFinset F d).mp hdF
      have hda : e.edgeEquiv a = d := e.edgeEquiv.apply_symm_apply d
      refine ⟨fun h => huv (congrArg e.vertexEquiv h), a, haF, ?_⟩
      change G.ends a = s(u, v)
      apply Sym2.map.injective e.vertexEquiv.injective
      rw [Sym2.map_mk, ← e.map_ends a, hda, hdlink]
    · rintro ⟨huv, a, haF, halink⟩
      refine ⟨e.vertexEquiv.injective.ne huv,
        e.edgeEquiv a, ?_, ?_⟩
      · exact Finset.mem_map.mpr ⟨a, haF, rfl⟩
      · change H.ends (e.edgeEquiv a) =
          s(e.vertexEquiv u, e.vertexEquiv v)
        rw [e.map_ends a, halink, Sym2.map_mk]

omit [Fintype E] in
/-- Relabelling preserves the labelled spanning-tree predicate. -/
theorem isSpanningTree_mapFinset_iff (e : Iso G H) (F : Finset E) :
    H.IsSpanningTree (e.mapFinset F) ↔ G.IsSpanningTree F := by
  constructor
  · intro h
    refine ⟨?_, (e.simpleGraphOnIso F).connected_iff.mpr h.selected_connected, ?_⟩
    · intro a haF haLoop
      have hmapMem : e.edgeEquiv a ∈ e.mapFinset F :=
        Finset.mem_map.mpr ⟨a, haF, rfl⟩
      apply h.loopless hmapMem
      change (H.ends (e.edgeEquiv a)).IsDiag
      rw [e.map_ends a]
      exact haLoop.map
    · have hc := h.card_edges_add_one
      rw [e.mapFinset_card F] at hc
      rw [Fintype.card_congr e.vertexEquiv]
      exact hc
  · intro h
    refine ⟨?_, (e.simpleGraphOnIso F).connected_iff.mp h.selected_connected, ?_⟩
    · intro d hdF hdLoop
      let a := e.edgeEquiv.symm d
      have haF : a ∈ F := (e.mem_mapFinset F d).mp hdF
      apply h.loopless haF
      apply (Sym2.isDiag_map e.vertexEquiv.injective).mp
      change (Sym2.map e.vertexEquiv (G.ends a)).IsDiag
      rw [← e.map_ends a, e.edgeEquiv.apply_symm_apply]
      exact hdLoop
    · rw [e.mapFinset_card F, h.card_edges_add_one]
      exact Fintype.card_congr e.vertexEquiv

/-- Reverse a simultaneous vertex/edge relabelling. -/
def symm (e : Iso G H) : Iso H G where
  vertexEquiv := e.vertexEquiv.symm
  edgeEquiv := e.edgeEquiv.symm
  map_ends := by
    intro d
    calc
      G.ends (e.edgeEquiv.symm d) =
          Sym2.map e.vertexEquiv.symm
            (Sym2.map e.vertexEquiv (G.ends (e.edgeEquiv.symm d))) := by
        rw [Sym2.map_map]
        simp
      _ = Sym2.map e.vertexEquiv.symm (H.ends d) := by
        rw [← e.map_ends (e.edgeEquiv.symm d)]
        simp

/-- Relabel every selected edge of a spanning tree. -/
def mapSpanningTree (e : Iso G H) (T : G.SpanningTree) : H.SpanningTree :=
  ⟨e.mapFinset T.1, (e.isSpanningTree_mapFinset_iff T.1).mpr T.2⟩

/-- A labelled-multigraph relabelling induces an equivalence of spanning
trees. -/
def spanningTreeEquiv (e : Iso G H) : G.SpanningTree ≃ H.SpanningTree where
  toFun := e.mapSpanningTree
  invFun := e.symm.mapSpanningTree
  left_inv T := by
    apply Subtype.ext
    ext a
    simp [mapSpanningTree, mapFinset, symm]
  right_inv T := by
    apply Subtype.ext
    ext d
    simp [mapSpanningTree, mapFinset, symm]

end Iso

/-- Connected-component quotients are canonically equivalent when their
reachability relations agree. -/
def componentEquivOfReachableEq
    (K L : SimpleGraph V) (hReach : K.Reachable = L.Reachable) :
    K.ConnectedComponent ≃ L.ConnectedComponent where
  toFun := SimpleGraph.ConnectedComponent.lift
    (fun v => L.connectedComponentMk v) (by
      intro u v p hp
      apply SimpleGraph.ConnectedComponent.sound
      rw [← hReach]
      exact p.reachable)
  invFun := SimpleGraph.ConnectedComponent.lift
    (fun v => K.connectedComponentMk v) (by
      intro u v p hp
      apply SimpleGraph.ConnectedComponent.sound
      rw [hReach]
      exact p.reachable)
  left_inv c := c.ind (fun _ => rfl)
  right_inv c := c.ind (fun _ => rfl)

omit [Fintype V] in
@[simp] theorem componentEquivOfReachableEq_mk
    (K L : SimpleGraph V) (hReach : K.Reachable = L.Reachable) (v : V) :
    componentEquivOfReachableEq K L hReach (K.connectedComponentMk v) =
      L.connectedComponentMk v :=
  rfl

variable (G : LabeledMultigraph V E)

omit [Fintype V] [Fintype E] in
/-- An original label collapses after contraction precisely according to the
reachability relation generated by the contracted labels. -/
theorem contractWithLoops_isLoop_iff_reachable
    (F : Finset E) (e : E) :
    (G.contractWithLoops F).IsLoop e ↔
      ∃ u v, G.IsLink e u v ∧
        (G.simpleGraphOn (F : Set E)).Reachable u v := by
  induction hends : G.ends e using Sym2.inductionOn with
  | _ u v =>
      constructor
      · intro h
        refine ⟨u, v, hends, ?_⟩
        change (Sym2.map (G.contractionMap F) (G.ends e)).IsDiag at h
        rw [hends, Sym2.map_mk, Sym2.mk_isDiag_iff] at h
        exact SimpleGraph.ConnectedComponent.exact h
      · rintro ⟨a, b, hab, hreach⟩
        have hpairs : s(a, b) = s(u, v) := hab.symm.trans hends
        have hcomp : G.contractionMap F a = G.contractionMap F b :=
          SimpleGraph.ConnectedComponent.sound hreach
        change (Sym2.map (G.contractionMap F) (G.ends e)).IsDiag
        rw [hends, ← hpairs, Sym2.map_mk, hcomp]
        exact Sym2.diag_isDiag _

omit [Fintype V] [Fintype E] in
/-- If two contracted label sets generate the same reachability relation,
an original label survives one contraction exactly when it survives the
other. -/
theorem contractWithLoops_isLoop_iff_of_reachable_eq
    (F X : Finset E)
    (hReach : (G.simpleGraphOn (F : Set E)).Reachable =
      (G.simpleGraphOn (X : Set E)).Reachable)
    (e : E) :
    (G.contractWithLoops F).IsLoop e ↔
      (G.contractWithLoops X).IsLoop e := by
  rw [contractWithLoops_isLoop_iff_reachable G F e,
    contractWithLoops_isLoop_iff_reachable G X e]
  simp only [hReach]

/-- Surviving labels of two reachability-equivalent contractions are
canonically equivalent, with the same underlying original label. -/
def contractionEdgeEquivOfReachableEq
    (F X : Finset E)
    (hReach : (G.simpleGraphOn (F : Set E)).Reachable =
      (G.simpleGraphOn (X : Set E)).Reachable) :
    (G.contractWithLoops F).NonLoopEdge ≃
      (G.contractWithLoops X).NonLoopEdge where
  toFun e := ⟨e.1, fun h => e.2
    ((contractWithLoops_isLoop_iff_of_reachable_eq G F X hReach e.1).mpr h)⟩
  invFun e := ⟨e.1, fun h => e.2
    ((contractWithLoops_isLoop_iff_of_reachable_eq G F X hReach e.1).mp h)⟩
  left_inv _ := rfl
  right_inv _ := rfl

omit [Fintype V] [Fintype E] in
@[simp] theorem contractionEdgeEquivOfReachableEq_val
    (F X : Finset E)
    (hReach : (G.simpleGraphOn (F : Set E)).Reachable =
      (G.simpleGraphOn (X : Set E)).Reachable)
    (e : (G.contractWithLoops F).NonLoopEdge) :
    (contractionEdgeEquivOfReachableEq G F X hReach e).1 = e.1 :=
  rfl

noncomputable local instance contractionNonLoopEdgeFintype (F : Finset E) :
    Fintype (G.contractWithLoops F).NonLoopEdge :=
  Fintype.ofFinite _

/-- Contracting reachability-equivalent label sets gives the same labelled
multigraph up to the canonical component and surviving-label relabellings. -/
def contractIsoOfReachableEq
    (F X : Finset E)
    (hReach : (G.simpleGraphOn (F : Set E)).Reachable =
      (G.simpleGraphOn (X : Set E)).Reachable) :
    Iso (G.contract F) (G.contract X) where
  vertexEquiv := componentEquivOfReachableEq
    (G.simpleGraphOn (F : Set E)) (G.simpleGraphOn (X : Set E)) hReach
  edgeEquiv := contractionEdgeEquivOfReachableEq G F X hReach
  map_ends := by
    intro e
    change Sym2.map (G.contractionMap X) (G.ends e.1) =
      Sym2.map
        (componentEquivOfReachableEq
          (G.simpleGraphOn (F : Set E))
          (G.simpleGraphOn (X : Set E)) hReach)
        (Sym2.map (G.contractionMap F) (G.ends e.1))
    induction hends : G.ends e.1 using Sym2.inductionOn with
    | _ u v =>
        rw [Sym2.map_mk, Sym2.map_mk, Sym2.map_mk]
        rfl

/-- The precise finite bridge used by forest events: a spanning forest and
the full vacancy-label set have equivalent contracted spanning-tree types as
soon as they generate the same components. -/
def contractSpanningTreeEquivOfReachableEq
    (F X : Finset E)
    (hReach : (G.simpleGraphOn (F : Set E)).Reachable =
      (G.simpleGraphOn (X : Set E)).Reachable) :
    (G.contract F).SpanningTree ≃ (G.contract X).SpanningTree :=
  (contractIsoOfReachableEq G F X hReach).spanningTreeEquiv

end ContractionRelabel

/-! ## Canonical labelled spanning forests -/

end
end Dual

namespace Multigraph.LabeledMultigraph

variable {V E : Type*} [Fintype V] [Fintype E]
variable (G : LabeledMultigraph V E)

/-- A chosen spanning forest of the simple graph supported by `X`. -/
noncomputable def spanningForestSubgraph (X : Finset E) : SimpleGraph V :=
  Classical.choose
    (G.simpleGraphOn (X : Set E)).exists_isAcyclic_reachable_eq_le

omit [Fintype V] [Fintype E] in
theorem spanningForestSubgraph_le (X : Finset E) :
    G.spanningForestSubgraph X ≤ G.simpleGraphOn (X : Set E) :=
  (Classical.choose_spec
    (G.simpleGraphOn (X : Set E)).exists_isAcyclic_reachable_eq_le).1

omit [Fintype V] [Fintype E] in
theorem spanningForestSubgraph_isAcyclic (X : Finset E) :
    (G.spanningForestSubgraph X).IsAcyclic :=
  (Classical.choose_spec
    (G.simpleGraphOn (X : Set E)).exists_isAcyclic_reachable_eq_le).2.1

omit [Fintype V] [Fintype E] in
theorem spanningForestSubgraph_reachable_eq (X : Finset E) :
    (G.spanningForestSubgraph X).Reachable =
      (G.simpleGraphOn (X : Set E)).Reachable :=
  (Classical.choose_spec
    (G.simpleGraphOn (X : Set E)).exists_isAcyclic_reachable_eq_le).2.2

omit [Fintype V] [Fintype E] in
private theorem exists_spanningForestLabel (X : Finset E)
    (p : (G.spanningForestSubgraph X).edgeSet) :
    ∃ e ∈ X, G.ends e = p.1 := by
  induction hp : p.1 using Sym2.inductionOn with
  | _ u v =>
      have huv : (G.spanningForestSubgraph X).Adj u v := by
        rw [← SimpleGraph.mem_edgeSet, ← hp]
        exact p.2
      rcases G.spanningForestSubgraph_le X huv with
        ⟨_huv, e, heX, hlink⟩
      exact ⟨e, heX, hlink⟩

/-- One ambient label chosen above each edge of the simple spanning forest. -/
noncomputable def spanningForestLabel (X : Finset E)
    (p : (G.spanningForestSubgraph X).edgeSet) : E :=
  Classical.choose (G.exists_spanningForestLabel X p)

omit [Fintype V] [Fintype E] in
@[simp] theorem spanningForestLabel_mem (X : Finset E)
    (p : (G.spanningForestSubgraph X).edgeSet) :
    G.spanningForestLabel X p ∈ X :=
  (Classical.choose_spec (G.exists_spanningForestLabel X p)).1

omit [Fintype V] [Fintype E] in
@[simp] theorem spanningForestLabel_ends (X : Finset E)
    (p : (G.spanningForestSubgraph X).edgeSet) :
    G.ends (G.spanningForestLabel X p) = p.1 :=
  (Classical.choose_spec (G.exists_spanningForestLabel X p)).2

omit [Fintype V] [Fintype E] in
theorem spanningForestLabel_injective (X : Finset E) :
    Function.Injective (G.spanningForestLabel X) := by
  intro p q hpq
  apply Subtype.ext
  rw [← G.spanningForestLabel_ends X p,
    ← G.spanningForestLabel_ends X q, hpq]

/-- The selected ambient labels of the chosen simple spanning forest. -/
noncomputable def spanningForestLabels (X : Finset E) : Finset E := by
  classical
  letI := Fintype.ofFinite (G.spanningForestSubgraph X).edgeSet
  exact Finset.univ.image (G.spanningForestLabel X)

omit [Fintype E] in
@[simp] theorem mem_spanningForestLabels (X : Finset E) (e : E) :
    e ∈ G.spanningForestLabels X ↔
      ∃ p : (G.spanningForestSubgraph X).edgeSet,
        G.spanningForestLabel X p = e := by
  classical
  simp [spanningForestLabels]

omit [Fintype E] in
theorem spanningForestLabels_subset (X : Finset E) :
    G.spanningForestLabels X ⊆ X := by
  intro e he
  obtain ⟨p, rfl⟩ := (G.mem_spanningForestLabels X e).mp he
  exact G.spanningForestLabel_mem X p

omit [Fintype E] in
/-- The labelled forest recovers the chosen simple spanning forest exactly. -/
theorem simpleGraphOn_spanningForestLabels (X : Finset E) :
    G.simpleGraphOn (G.spanningForestLabels X : Set E) =
      G.spanningForestSubgraph X := by
  ext u v
  constructor
  · rintro ⟨huv, e, he, hlink⟩
    obtain ⟨p, rfl⟩ := (G.mem_spanningForestLabels X e).mp he
    have hpEnds := G.spanningForestLabel_ends X p
    have hpPair : p.1 = s(u, v) := hpEnds.symm.trans hlink
    rw [← SimpleGraph.mem_edgeSet, ← hpPair]
    exact p.2
  · intro huv
    let p : (G.spanningForestSubgraph X).edgeSet := ⟨s(u, v), huv⟩
    refine ⟨huv.ne, G.spanningForestLabel X p, ?_, ?_⟩
    · exact (G.mem_spanningForestLabels X _).mpr ⟨p, rfl⟩
    · exact G.spanningForestLabel_ends X p

omit [Fintype E] in
/-- The selected labels generate exactly the same contraction components as
the full label set `X`. -/
theorem spanningForestLabels_reachable_eq (X : Finset E) :
    (G.simpleGraphOn (G.spanningForestLabels X : Set E)).Reachable =
      (G.simpleGraphOn (X : Set E)).Reachable := by
  rw [G.simpleGraphOn_spanningForestLabels X]
  exact G.spanningForestSubgraph_reachable_eq X

omit [Fintype V] [Fintype E] in
private theorem exists_extensionLabel
    {U : SimpleGraph V} (hUG : U ≤ G.toSimpleGraph)
    (p : U.edgeSet) : ∃ e, G.ends e = p.1 := by
  induction hp : p.1 using Sym2.inductionOn with
  | _ u v =>
      have huv : U.Adj u v := by
        rw [← SimpleGraph.mem_edgeSet, ← hp]
        exact p.2
      rcases hUG huv with ⟨_huv, e, hlink⟩
      exact ⟨e, hlink⟩

/-- In a connected ambient labelled graph, the chosen spanning-forest labels
extend to a labelled spanning tree. -/
theorem spanningForestLabels_isEdgeForest
    (hG : G.Connected) (X : Finset E) :
    G.IsEdgeForest (G.spanningForestLabels X) := by
  classical
  let T := G.spanningForestSubgraph X
  have hTG : T ≤ G.toSimpleGraph := by
    rw [← G.simpleGraphOn_univ]
    exact (G.spanningForestSubgraph_le X).trans
      (G.simpleGraphOn_mono (Set.subset_univ _))
  obtain ⟨U, hTU, hUG, hUtree⟩ :=
    hG.exists_isTree_le_of_le_of_isAcyclic hTG
      (G.spanningForestSubgraph_isAcyclic X)
  let extensionLabel : U.edgeSet → E := fun p =>
    if hp : p.1 ∈ T.edgeSet then
      G.spanningForestLabel X ⟨p.1, hp⟩
    else Classical.choose (G.exists_extensionLabel hUG p)
  have extensionLabel_ends (p : U.edgeSet) :
      G.ends (extensionLabel p) = p.1 := by
    dsimp only [extensionLabel]
    split
    · exact G.spanningForestLabel_ends X _
    · exact Classical.choose_spec (G.exists_extensionLabel hUG p)
  have extensionLabel_injective : Function.Injective extensionLabel := by
    intro p q hpq
    apply Subtype.ext
    rw [← extensionLabel_ends p, ← extensionLabel_ends q, hpq]
  let treeLabels : Finset E := by
    letI := Fintype.ofFinite U.edgeSet
    exact Finset.univ.image extensionLabel
  have mem_treeLabels (e : E) :
      e ∈ treeLabels ↔ ∃ p : U.edgeSet, extensionLabel p = e := by
    letI := Fintype.ofFinite U.edgeSet
    simp [treeLabels]
  have simpleGraphOn_treeLabels :
      G.simpleGraphOn (treeLabels : Set E) = U := by
    ext u v
    constructor
    · rintro ⟨huv, e, he, hlink⟩
      obtain ⟨p, rfl⟩ := (mem_treeLabels e).mp he
      have hpPair : p.1 = s(u, v) :=
        (extensionLabel_ends p).symm.trans hlink
      rw [← SimpleGraph.mem_edgeSet, ← hpPair]
      exact p.2
    · intro huv
      let p : U.edgeSet := ⟨s(u, v), huv⟩
      refine ⟨huv.ne, extensionLabel p, ?_, extensionLabel_ends p⟩
      exact (mem_treeLabels _).mpr ⟨p, rfl⟩
  have treeLabels_isSpanningTree : G.IsSpanningTree treeLabels := by
    refine ⟨?_, ?_, ?_⟩
    · intro e he hloop
      obtain ⟨p, rfl⟩ := (mem_treeLabels e).mp he
      apply U.not_isDiag_of_mem_edgeSet p.2
      rw [← extensionLabel_ends p]
      exact hloop
    · rw [simpleGraphOn_treeLabels]
      exact hUtree.connected
    · letI := Fintype.ofFinite U.edgeSet
      have hcard : treeLabels.card = Fintype.card U.edgeSet := by
        dsimp only [treeLabels]
        rw [Finset.card_image_of_injective]
        · simp
        · exact extensionLabel_injective
      rw [hcard]
      rw [← SimpleGraph.edgeFinset_card]
      exact hUtree.card_edgeFinset
  refine ⟨⟨treeLabels, treeLabels_isSpanningTree⟩, ?_⟩
  intro e he
  obtain ⟨p, rfl⟩ := (G.mem_spanningForestLabels X e).mp he
  have hpU : p.1 ∈ U.edgeSet := by
    induction hp : p.1 using Sym2.inductionOn with
    | _ u v =>
        rw [SimpleGraph.mem_edgeSet]
        apply hTU
        rw [← SimpleGraph.mem_edgeSet, ← hp]
        exact p.2
  let q : U.edgeSet := ⟨p.1, hpU⟩
  apply (mem_treeLabels _).mpr
  refine ⟨q, ?_⟩
  simp [extensionLabel, q, T, p.2]

/-- A loopless labelled set with no parallel selected labels is a graphic
forest as soon as its selected underlying simple graph is acyclic.  The proof
identifies the set with the canonical chosen labelled spanning forest above. -/
theorem isEdgeForest_of_simpleGraphOn_isAcyclic
    (hG : G.Connected) {F : Finset E}
    (hloop : ∀ e ∈ F, ¬G.IsLoop e)
    (hends : ∀ e ∈ F, ∀ d ∈ F, G.ends e = G.ends d → e = d)
    (hacyc : (G.simpleGraphOn (F : Set E)).IsAcyclic) :
    G.IsEdgeForest F := by
  classical
  let K := G.simpleGraphOn (F : Set E)
  let T := G.spanningForestSubgraph F
  have hTK : T ≤ K := G.spanningForestSubgraph_le F
  have hTacyc : T.IsAcyclic := G.spanningForestSubgraph_isAcyclic F
  have hTreach : T.Reachable = K.Reachable :=
    G.spanningForestSubgraph_reachable_eq F
  have hTmax : Maximal (fun H ↦ H ≤ K ∧ H.IsAcyclic) T :=
    (K.maximal_isAcyclic_iff_reachable_eq hTK hTacyc).mpr hTreach
  have hTKeq : T = K :=
    le_antisymm hTK (hTmax.le_of_ge ⟨le_rfl, hacyc⟩ hTK)
  have hlabels : G.spanningForestLabels F = F := by
    apply Finset.Subset.antisymm (G.spanningForestLabels_subset F)
    intro e heF
    induction heEnds : G.ends e using Sym2.inductionOn with
    | _ u v =>
        have huv : u ≠ v := by
          intro huv
          apply hloop e heF
          change (G.ends e).IsDiag
          rw [heEnds, huv]
          exact Sym2.diag_isDiag _
        have hKuv : K.Adj u v := ⟨huv, e, heF, heEnds⟩
        have hTuv : T.Adj u v := by rw [hTKeq]; exact hKuv
        let p : T.edgeSet := ⟨s(u, v), hTuv⟩
        have hchosenMem : G.spanningForestLabel F p ∈ F :=
          G.spanningForestLabel_mem F p
        have hchosenEnds : G.ends (G.spanningForestLabel F p) = G.ends e := by
          rw [G.spanningForestLabel_ends F p, heEnds]
        have hchosenEq : G.spanningForestLabel F p = e :=
          hends _ hchosenMem e heF hchosenEnds
        exact (G.mem_spanningForestLabels F e).mpr ⟨p, hchosenEq⟩
  rw [← hlabels]
  exact G.spanningForestLabels_isEdgeForest hG F

/-- A walk in the chosen forest of a union of vertex-disjoint graph blocks
cannot leave the block containing its initial vertex.  The resulting walk
uses the original chosen labels as well as that block's labels. -/
noncomputable def restrictSpanningForestWalkToBlock
    {ι : Type*} [Fintype ι]
    (B : ι → Finset E)
    (hSupport : Pairwise fun i j ↦
      Disjoint
        (G.simpleGraphOn (B i : Set E)).support
        (G.simpleGraphOn (B j : Set E)).support)
    (i : ι) {u v : V}
    (p : (G.simpleGraphOn
      (G.spanningForestLabels (unionEdgeBlocks B) : Set E)).Walk u v)
    (hu : u ∈ (G.simpleGraphOn (B i : Set E)).support) :
    (G.simpleGraphOn
      (G.spanningForestLabels (unionEdgeBlocks B) ∩ B i : Set E)).Walk u v := by
  classical
  induction p with
  | nil => exact .nil
  | @cons u v w huv p ih =>
      have hstep :
          (G.simpleGraphOn
            (G.spanningForestLabels (unionEdgeBlocks B) ∩ B i :
              Set E)).Adj u v ∧
          v ∈ (G.simpleGraphOn (B i : Set E)).support := by
        rcases huv with ⟨huvne, e, heForest, hends⟩
        have heUnion : e ∈ unionEdgeBlocks B :=
          G.spanningForestLabels_subset (unionEdgeBlocks B) heForest
        rcases mem_unionEdgeBlocks.mp heUnion with ⟨j, hej⟩
        have huvj : (G.simpleGraphOn (B j : Set E)).Adj u v :=
          ⟨huvne, e, hej, hends⟩
        have huj : u ∈ (G.simpleGraphOn (B j : Set E)).support :=
          (SimpleGraph.mem_support _).mpr ⟨v, huvj⟩
        have hji : j = i := by
          by_contra hne
          exact Set.disjoint_left.mp (hSupport hne) huj hu
        subst j
        exact ⟨⟨huvne, e, ⟨heForest, hej⟩, hends⟩,
          (SimpleGraph.mem_support _).mpr ⟨u, huvj.symm⟩⟩
      exact .cons hstep.1 (ih hstep.2)

omit [Fintype E] in
/-- Restricting the chosen labelled spanning forest of a union of
vertex-disjoint blocks to one block preserves that block's reachability
relation. -/
theorem spanningForestLabels_inter_reachable_eq
    {ι : Type*} [Fintype ι]
    (B : ι → Finset E)
    (hSupport : Pairwise fun i j ↦
      Disjoint
        (G.simpleGraphOn (B i : Set E)).support
        (G.simpleGraphOn (B j : Set E)).support)
    (i : ι) :
    (G.simpleGraphOn
      (G.spanningForestLabels (unionEdgeBlocks B) ∩ B i : Set E)).Reachable =
    (G.simpleGraphOn (B i : Set E)).Reachable := by
  classical
  apply funext
  intro u
  apply funext
  intro v
  apply propext
  constructor
  · intro huv
    exact huv.mono (G.simpleGraphOn_mono Set.inter_subset_right)
  · intro huv
    by_cases huvEq : u = v
    · subst v
      rfl
    · have hu : u ∈ (G.simpleGraphOn (B i : Set E)).support :=
        (SimpleGraph.mem_support _).mpr
          (huv.nonempty_neighborSet_left huvEq)
      have hBlockUnion : B i ⊆ unionEdgeBlocks B := by
        intro e he
        exact mem_unionEdgeBlocks.mpr ⟨i, he⟩
      have huvUnion : (G.simpleGraphOn
          (unionEdgeBlocks B : Set E)).Reachable u v :=
        huv.mono (G.simpleGraphOn_mono hBlockUnion)
      have huvForest : (G.simpleGraphOn
          (G.spanningForestLabels (unionEdgeBlocks B) : Set E)).Reachable u v := by
        rw [G.spanningForestLabels_reachable_eq]
        exact huvUnion
      rcases huvForest with ⟨p⟩
      exact ⟨G.restrictSpanningForestWalkToBlock B hSupport i p hu⟩

end Multigraph.LabeledMultigraph

namespace Dual

open Multigraph
open Multigraph.LabeledMultigraph

noncomputable section

/-! ## Tree-count transport from deletion complements -/

/-- The tree equivalence supplied by an all-vacancy deletion/complement law.
The geometric law constructs this equivalence by complementing primal labels;
the present module uses only its finite type after that construction. -/
abbrev VacancyDeletionTreeEquiv
    (R S : ℕ) (X : Finset (Fin (R + 1) × Fin (S + 1)))
    (D : Finset Point) :=
  SimpleSpanningTreeType (inducedGrid D) ≃
    ((rectangleDual (R + 1) (S + 1)).contract
      (vacancyDualEdges X)).SpanningTree

/-- The exact deletion/complement family needed for one canonical hull: the
whole vacancy set, its boundary-attached component, and every interior
component.  No probability or determinant statement is included. -/
structure CanonicalVacancyDeletionTreeEquivs
    (A : Finset Point) (R S : ℕ) : Type where
  whole : VacancyDeletionTreeEquiv R S
    (encodedPrimalVacancies R S A) A
  boundary : VacancyDeletionTreeEquiv R S
    (canonicalBoundaryPrimal R S A)
    (rectangle 0 0 (R + 1) (S + 1) \
      Boundary.canonicalBoundary R S A)
  interior : ∀ i, VacancyDeletionTreeEquiv R S
    (canonicalInteriorPrimal R S A i)
    (rectangle 0 0 (R + 1) (S + 1) \
      Boundary.canonicalInterior R S A i)

/-- Full rectangle complementation identifies the ambient dual tree count
with `tauRect`. -/
theorem rectangleDual_spanningTreeCount_eq_tauRect_of_complementLaw
    (R S : ℕ)
    (hRectangle : RectangleTreeComplementLaw (R + 1) (S + 1)) :
    (rectangleDual (R + 1) (S + 1)).spanningTreeCount =
      tauRect (R + 1) (S + 1) := by
  unfold LabeledMultigraph.spanningTreeCount tauRect tau treeCount
  exact Nat.card_congr
    (rectangleTreeEquivOfComplementLaw R S hRectangle).symm

/-- Contracting a forest event, replacing it by the reachability-equivalent
full vacancy set, and applying planar deletion complementation gives the
exact containment count. -/
theorem containmentCount_eq_tau_of_vacancyDeletionTreeEquiv
    (R S : ℕ) (X : Finset (Fin (R + 1) × Fin (S + 1)))
    (D : Finset Point)
    (F : Finset (RectangleEdge (R + 1) (S + 1)))
    (hF : (rectangleDual (R + 1) (S + 1)).IsEdgeForest F)
    (hReach :
      ((rectangleDual (R + 1) (S + 1)).simpleGraphOn
        (F : Set (RectangleEdge (R + 1) (S + 1)))).Reachable =
      ((rectangleDual (R + 1) (S + 1)).simpleGraphOn
        (vacancyDualEdges X : Set (RectangleEdge (R + 1) (S + 1)))).Reachable)
    (hDeletion : VacancyDeletionTreeEquiv R S X D) :
    (rectangleDual (R + 1) (S + 1)).containmentCount F = tau D := by
  let G := rectangleDual (R + 1) (S + 1)
  calc
    G.containmentCount F = (G.contract F).spanningTreeCount :=
      G.containmentCount_eq_spanningTreeCount_contract hF
    _ = (G.contract (vacancyDualEdges X)).spanningTreeCount := by
      unfold LabeledMultigraph.spanningTreeCount
      exact Nat.card_congr
        (ContractionRelabel.contractSpanningTreeEquivOfReachableEq
          G F (vacancyDualEdges X) hReach)
    _ = tau D := by
      unfold LabeledMultigraph.spanningTreeCount tau treeCount
      exact Nat.card_congr hDeletion.symm

/-- Ratio form of the preceding finite count identity. -/
theorem containmentRatio_eq_tau_div_tauRect_of_complementLaws
    (R S : ℕ) (X : Finset (Fin (R + 1) × Fin (S + 1)))
    (D : Finset Point)
    (F : Finset (RectangleEdge (R + 1) (S + 1)))
    (hF : (rectangleDual (R + 1) (S + 1)).IsEdgeForest F)
    (hReach :
      ((rectangleDual (R + 1) (S + 1)).simpleGraphOn
        (F : Set (RectangleEdge (R + 1) (S + 1)))).Reachable =
      ((rectangleDual (R + 1) (S + 1)).simpleGraphOn
        (vacancyDualEdges X : Set (RectangleEdge (R + 1) (S + 1)))).Reachable)
    (hRectangle : RectangleTreeComplementLaw (R + 1) (S + 1))
    (hDeletion : VacancyDeletionTreeEquiv R S X D) :
    (rectangleDual (R + 1) (S + 1)).containmentRatio F =
      (tau D : ℝ) / (tauRect (R + 1) (S + 1) : ℝ) := by
  unfold LabeledMultigraph.containmentRatio
  rw [containmentCount_eq_tau_of_vacancyDeletionTreeEquiv
      R S X D F hF hReach hDeletion,
    rectangleDual_spanningTreeCount_eq_tauRect_of_complementLaw
      R S hRectangle]

/-! ## One global forest, restricted to the canonical components -/

/-- A single chosen spanning forest of all dual labels generated by the
encoded vacancies.  Using one global forest makes the union-forest field of
`CanonicalForestEvents` automatic. -/
noncomputable def canonicalGlobalVacancyForest
    (R S : ℕ) (A : Finset Point) :
    Finset (RectangleEdge (R + 1) (S + 1)) :=
  (rectangleDual (R + 1) (S + 1)).spanningForestLabels
    (vacancyDualEdges (encodedPrimalVacancies R S A))

/-- Restrict the global forest to one boundary/interior canonical label
block. -/
noncomputable def canonicalGlobalVacancyForestBlock
    (R S : ℕ) (A : Finset Point)
    (i : Option (Fin (Boundary.canonicalInteriorCount R S A))) :
    Finset (RectangleEdge (R + 1) (S + 1)) :=
  canonicalGlobalVacancyForest R S A ∩ canonicalDualEdgeBlock R S A i

theorem canonicalGlobalVacancyForestBlock_subset
    (R S : ℕ) (A : Finset Point)
    (i : Option (Fin (Boundary.canonicalInteriorCount R S A))) :
    canonicalGlobalVacancyForestBlock R S A i ⊆
      canonicalDualEdgeBlock R S A i :=
  Finset.inter_subset_right

/-- The canonical blocks partition the chosen global forest. -/
theorem unionEdgeBlocks_canonicalGlobalVacancyForestBlock
    (R S : ℕ) (A : Finset Point) :
    LabeledMultigraph.unionEdgeBlocks
      (canonicalGlobalVacancyForestBlock R S A) =
        canonicalGlobalVacancyForest R S A := by
  classical
  ext e
  rw [LabeledMultigraph.mem_unionEdgeBlocks]
  constructor
  · rintro ⟨i, hi⟩
    exact (Finset.mem_inter.mp hi).1
  · intro he
    have heFull : e ∈ vacancyDualEdges (encodedPrimalVacancies R S A) :=
      (rectangleDual (R + 1) (S + 1)).spanningForestLabels_subset _ he
    rw [← unionEdgeBlocks_canonicalDualEdgeBlock R S A,
      LabeledMultigraph.mem_unionEdgeBlocks] at heFull
    rcases heFull with ⟨i, hi⟩
    exact ⟨i, Finset.mem_inter.mpr ⟨he, hi⟩⟩

/-- The exact remaining component-separation fact for the global forest:
restricting it to one canonical edge block still spans every component of
that block.  This is strictly weaker than any deletion/tree-count identity. -/
def CanonicalGlobalForestRestrictionLaw
    (R S : ℕ) (A : Finset Point) : Prop :=
  ∀ i : Option (Fin (Boundary.canonicalInteriorCount R S A)),
    ((rectangleDual (R + 1) (S + 1)).simpleGraphOn
      (canonicalGlobalVacancyForestBlock R S A i :
        Set (RectangleEdge (R + 1) (S + 1)))).Reachable =
    ((rectangleDual (R + 1) (S + 1)).simpleGraphOn
      (canonicalDualEdgeBlock R S A i :
        Set (RectangleEdge (R + 1) (S + 1)))).Reachable

/-- Rectangle and deletion complement laws construct the entire canonical
forest-event package once the primitive component-restriction fact above is
known. -/
noncomputable def canonicalForestEventsOfDeletionComplementLawsAndRestriction
    (R S : ℕ) (A : Finset Point)
    (hRectangle : RectangleTreeComplementLaw (R + 1) (S + 1))
    (hRestriction : CanonicalGlobalForestRestrictionLaw R S A)
    (hWhole : VacancyDeletionTreeEquiv R S
      (encodedPrimalVacancies R S A) A)
    (hBoundary : VacancyDeletionTreeEquiv R S
      (canonicalBoundaryPrimal R S A)
      (rectangle 0 0 (R + 1) (S + 1) \
        Boundary.canonicalBoundary R S A))
    (hInterior : ∀ i, VacancyDeletionTreeEquiv R S
      (canonicalInteriorPrimal R S A i)
      (rectangle 0 0 (R + 1) (S + 1) \
        Boundary.canonicalInterior R S A i)) :
    CanonicalForestEvents A R S := by
  let G := rectangleDual (R + 1) (S + 1)
  have hGconn : G.Connected := rectangleDual_connected_pos (by omega) (by omega)
  have hGlobalForest : G.IsEdgeForest
      (canonicalGlobalVacancyForest R S A) :=
    G.spanningForestLabels_isEdgeForest hGconn _
  have hBlockForest (i) : G.IsEdgeForest
      (canonicalGlobalVacancyForestBlock R S A i) :=
    G.isEdgeForest_mono hGlobalForest Finset.inter_subset_left
  refine {
    block := canonicalGlobalVacancyForestBlock R S A
    block_subset := canonicalGlobalVacancyForestBlock_subset R S A
    unionForest := ?_
    ambientPositive := LabeledMultigraph.spanningTreeCount_pos_of_connected
      G hGconn
    wholeEvent := ?_
    boundaryEvent := ?_
    interiorEvent := ?_
  }
  · rw [unionEdgeBlocks_canonicalGlobalVacancyForestBlock]
    exact hGlobalForest
  · rw [unionEdgeBlocks_canonicalGlobalVacancyForestBlock]
    exact containmentRatio_eq_tau_div_tauRect_of_complementLaws
      R S (encodedPrimalVacancies R S A) A
      (canonicalGlobalVacancyForest R S A) hGlobalForest
      (G.spanningForestLabels_reachable_eq _) hRectangle hWhole
  · exact containmentRatio_eq_tau_div_tauRect_of_complementLaws
      R S (canonicalBoundaryPrimal R S A)
      (rectangle 0 0 (R + 1) (S + 1) \
        Boundary.canonicalBoundary R S A)
      (canonicalGlobalVacancyForestBlock R S A none)
      (hBlockForest none) (hRestriction none) hRectangle hBoundary
  · intro i
    exact containmentRatio_eq_tau_div_tauRect_of_complementLaws
      R S (canonicalInteriorPrimal R S A i)
      (rectangle 0 0 (R + 1) (S + 1) \
        Boundary.canonicalInterior R S A i)
      (canonicalGlobalVacancyForestBlock R S A (some i))
      (hBlockForest (some i)) (hRestriction (some i)) hRectangle
      (hInterior i)

/-! ## Interior event-family constructor -/

/-- Construct all per-tree interior planar-duality count identities from the
same rectangle/deletion complement family.  The hypotheses on each explicit
face-star block are purely the forest and component-spanning facts. -/
theorem interiorPlanarDualityInputOfDeletionComplementLawsAndForestReach
    (R S : ℕ) (A : Finset Point)
    (i : Fin (Boundary.canonicalInteriorCount R S A))
    (hRectangle : RectangleTreeComplementLaw (R + 1) (S + 1))
    (hDeletion : VacancyDeletionTreeEquiv R S
      (canonicalInteriorPrimal R S A i)
      (rectangle 0 0 (R + 1) (S + 1) \
        Boundary.canonicalInterior R S A i))
    (hForest : ∀ j, (rectangleDual (R + 1) (S + 1)).IsEdgeForest
      (interiorEventBlock R S A i j))
    (hReach : ∀ j,
      ((rectangleDual (R + 1) (S + 1)).simpleGraphOn
        (interiorEventBlock R S A i j :
          Set (RectangleEdge (R + 1) (S + 1)))).Reachable =
      ((rectangleDual (R + 1) (S + 1)).simpleGraphOn
        (vacancyDualEdges (canonicalInteriorPrimal R S A i) :
          Set (RectangleEdge (R + 1) (S + 1)))).Reachable) :
    InteriorPlanarDualityInput A R S i where
  rectangleTreeCount :=
    rectangleDual_spanningTreeCount_eq_tauRect_of_complementLaw
      R S hRectangle
  containmentTreeCount j :=
    containmentCount_eq_tau_of_vacancyDeletionTreeEquiv
      R S (canonicalInteriorPrimal R S A i)
      (rectangle 0 0 (R + 1) (S + 1) \
        Boundary.canonicalInterior R S A i)
      (interiorEventBlock R S A i j) (hForest j) (hReach j) hDeletion

/-! ## Geometry of interior event blocks -/

/-- If a primal endpoint of a rectangular label is selected and the dual
label meets the exterior face, that primal endpoint lies on the perimeter. -/
theorem isPerimeter_of_primalIncident_of_none_mem_rectangleDual_ends
    {R S : ℕ} (p : Fin (R + 1) × Fin (S + 1))
    (e : RectangleEdge (R + 1) (S + 1))
    (hp : PrimalIncident p e)
    (heNone : none ∈ (rectangleDual (R + 1) (S + 1)).ends e) :
    Boundary.IsPerimeter R S (finPoint p) := by
  cases e with
  | horizontal e =>
      change p = horizontalPrimalLeft e ∨
        p = horizontalPrimalRight e at hp
      change none ∈ s(horizontalBelow e, horizontalAbove e) at heNone
      rcases Sym2.mem_iff.mp heNone with hbelow | habove
      · have hy : e.y.1 = 0 :=
          (horizontalBelow_eq_none_iff e).mp hbelow.symm
        rcases hp with rfl | rfl <;>
          simp [Boundary.IsPerimeter, finPoint, horizontalPrimalLeft,
            horizontalPrimalRight, hy]
      · have hy : ¬e.y.1 + 1 < S + 1 :=
          (horizontalAbove_eq_none_iff e).mp habove.symm
        rcases hp with rfl | rfl <;>
          simp only [Boundary.IsPerimeter, finPoint, horizontalPrimalLeft,
            horizontalPrimalRight]
        all_goals right; right; right; omega
  | vertical e =>
      change p = verticalPrimalBottom e ∨ p = verticalPrimalTop e at hp
      change none ∈ s(verticalLeft e, verticalRight e) at heNone
      rcases Sym2.mem_iff.mp heNone with hleft | hright
      · have hx : e.x.1 = 0 :=
          (verticalLeft_eq_none_iff e).mp hleft.symm
        rcases hp with rfl | rfl <;>
          simp [Boundary.IsPerimeter, finPoint, verticalPrimalBottom,
            verticalPrimalTop, hx]
      · have hx : ¬e.x.1 + 1 < R + 1 :=
          (verticalRight_eq_none_iff e).mp hright.symm
        rcases hp with rfl | rfl <;>
          simp only [Boundary.IsPerimeter, finPoint, verticalPrimalBottom,
            verticalPrimalTop]
        all_goals right; left; omega

/-- A vacancy set avoiding the primal perimeter generates no selected dual
edge incident with the exterior face. -/
theorem dualEdgeGraph_not_adj_none_of_not_perimeter
    {R S : ℕ} {X : Finset (Fin (R + 1) × Fin (S + 1))}
    (hX : ∀ p ∈ X, ¬Boundary.IsPerimeter R S (finPoint p))
    (v : RectangleDualVertex (R + 1) (S + 1)) :
    ¬(dualEdgeGraph X).Adj none v := by
  rintro ⟨_hne, e, heX, hlink⟩
  rcases mem_vacancyDualEdges.mp heX with ⟨p, hpX, hpinc⟩
  apply hX p hpX
  apply isPerimeter_of_primalIncident_of_none_mem_rectangleDual_ends p e hpinc
  rw [hlink]
  exact Sym2.mem_mk_left _ _

/-- Two distinct primal grid vertices occurring as corners of one bounded
unit face are king-adjacent. -/
theorem kingAdjacent_of_ne_of_mem_same_faceCorners
    {R S : ℕ} (p q : Fin (R + 1) × Fin (S + 1))
    (f : BoundedFace (R + 1) (S + 1))
    (hpq : p ≠ q)
    (hp : finPoint p ∈ Boundary.faceCorners (f.1.1, f.2.1))
    (hq : finPoint q ∈ Boundary.faceCorners (f.1.1, f.2.1)) :
    Boundary.KingAdjacent (finPoint p) (finPoint q) := by
  rw [Boundary.mem_faceCorners] at hp hq
  simp only [finPoint] at hp hq
  refine ⟨finPoint_injective.ne hpq, ?_, ?_⟩
  · simp only [finPoint]
    simp [Nat.dist]
    omega
  · simp only [finPoint]
    simp [Nat.dist]
    omega

/-- A bounded dual face in the support of a vacancy edge graph has a
selected primal corner. -/
theorem exists_selected_corner_of_mem_dualEdgeGraph_support_some
    {R S : ℕ} {X : Finset (Fin (R + 1) × Fin (S + 1))}
    (f : BoundedFace (R + 1) (S + 1))
    (hf : some f ∈ (dualEdgeGraph X).support) :
    ∃ p ∈ X, finPoint p ∈ Boundary.faceCorners (f.1.1, f.2.1) := by
  rw [SimpleGraph.mem_support] at hf
  rcases hf with ⟨v, hfv⟩
  rw [dualEdgeGraph_adj_iff] at hfv
  rcases hfv with ⟨_hne, e, heX, hlink⟩
  have heIncident : some f ∈
      (rectangleDual (R + 1) (S + 1)).ends e := by
    rw [hlink]
    exact Sym2.mem_mk_left _ _
  rcases faceSideEdge_surjective_incident f ⟨e, heIncident⟩ with ⟨d, hd⟩
  rcases mem_vacancyDualEdges.mp heX with ⟨p, hpX, hpe⟩
  refine ⟨p, hpX,
    finPoint_mem_faceCorners_of_primalIncident_faceSideEdge f d p ?_⟩
  exact hd.symm ▸ hpe

/-- King-separated primal sets have vertex-disjoint selected dual supports
provided the second set avoids the perimeter.  The perimeter condition
excludes the only exceptional shared vertex, the exterior face. -/
theorem disjoint_dualEdgeGraph_support_of_kingSeparated_of_not_perimeter
    {R S : ℕ}
    {X Y : Finset (Fin (R + 1) × Fin (S + 1))}
    (hsep : ∀ p ∈ X, ∀ q ∈ Y,
      p ≠ q ∧ ¬Boundary.KingAdjacent (finPoint p) (finPoint q))
    (hY : ∀ q ∈ Y, ¬Boundary.IsPerimeter R S (finPoint q)) :
    Disjoint (dualEdgeGraph X).support (dualEdgeGraph Y).support := by
  rw [Set.disjoint_left]
  intro v hvX hvY
  cases v with
  | none =>
      rw [SimpleGraph.mem_support] at hvY
      rcases hvY with ⟨w, hyw⟩
      exact dualEdgeGraph_not_adj_none_of_not_perimeter hY w hyw
  | some f =>
      rcases exists_selected_corner_of_mem_dualEdgeGraph_support_some f hvX with
        ⟨p, hpX, hpf⟩
      rcases exists_selected_corner_of_mem_dualEdgeGraph_support_some f hvY with
        ⟨q, hqY, hqf⟩
      have hpq := hsep p hpX q hqY
      exact hpq.2
        (kingAdjacent_of_ne_of_mem_same_faceCorners p q f hpq.1 hpf hqf)

/-- In particular the exterior is isolated in the dual graph generated by a
canonical interior vacancy component. -/
theorem canonicalInterior_dualEdgeGraph_neighborSet_none
    (R S : ℕ) (A : Finset Point)
    (i : Fin (Boundary.canonicalInteriorCount R S A)) :
    (dualEdgeGraph (canonicalInteriorPrimal R S A i)).neighborSet none = ∅ := by
  ext v
  simp only [SimpleGraph.mem_neighborSet, Set.mem_empty_iff_false, iff_false]
  exact dualEdgeGraph_not_adj_none_of_not_perimeter
    (fun _ hp => canonicalInteriorPrimal_not_perimeter hp) v

/-- Distinct canonical vacancy components have vertex-disjoint selected
dual supports, not merely disjoint label sets. -/
theorem canonicalDualEdgeBlock_support_pairwiseDisjoint
    (R S : ℕ) (A : Finset Point) :
    Pairwise fun i j ↦
      Disjoint
        ((rectangleDual (R + 1) (S + 1)).simpleGraphOn
          (canonicalDualEdgeBlock R S A i :
            Set (RectangleEdge (R + 1) (S + 1)))).support
        ((rectangleDual (R + 1) (S + 1)).simpleGraphOn
          (canonicalDualEdgeBlock R S A j :
            Set (RectangleEdge (R + 1) (S + 1)))).support := by
  intro i j hij
  cases i with
  | none =>
      cases j with
      | none => exact (hij rfl).elim
      | some j =>
          simpa [canonicalDualEdgeBlock, dualEdgeGraph] using
            (disjoint_dualEdgeGraph_support_of_kingSeparated_of_not_perimeter
              (kingSeparated_boundary_interior R S A j)
              (fun _ hp => canonicalInteriorPrimal_not_perimeter hp))
  | some i =>
      cases j with
      | none =>
          simpa [canonicalDualEdgeBlock, dualEdgeGraph] using
            (disjoint_dualEdgeGraph_support_of_kingSeparated_of_not_perimeter
              (kingSeparated_boundary_interior R S A i)
              (fun _ hp => canonicalInteriorPrimal_not_perimeter hp)).symm
      | some j =>
          have hij' : i ≠ j := by
            intro h
            exact hij (congrArg some h)
          simpa [canonicalDualEdgeBlock, dualEdgeGraph] using
            (disjoint_dualEdgeGraph_support_of_kingSeparated_of_not_perimeter
              (kingSeparated_interior R S A hij')
              (fun _ hp => canonicalInteriorPrimal_not_perimeter hp))

/-- The global chosen vacancy forest restricts to a spanning forest of every
canonical vacancy component. -/
theorem canonicalGlobalForestRestrictionLaw
    (R S : ℕ) (A : Finset Point) :
    CanonicalGlobalForestRestrictionLaw R S A := by
  intro i
  let G := rectangleDual (R + 1) (S + 1)
  have h := G.spanningForestLabels_inter_reachable_eq
    (canonicalDualEdgeBlock R S A)
    (canonicalDualEdgeBlock_support_pairwiseDisjoint R S A) i
  rw [unionEdgeBlocks_canonicalDualEdgeBlock R S A] at h
  simpa [G, canonicalGlobalVacancyForestBlock,
    canonicalGlobalVacancyForest] using h

/-- Rectangle complementation plus one deletion/contraction tree equivalence
for the whole vacancy set and for each canonical component constructs the
complete canonical forest-event package. -/
noncomputable def canonicalForestEventsOfDeletionComplementLaws
    (R S : ℕ) (A : Finset Point)
    (hRectangle : RectangleTreeComplementLaw (R + 1) (S + 1))
    (hWhole : VacancyDeletionTreeEquiv R S
      (encodedPrimalVacancies R S A) A)
    (hBoundary : VacancyDeletionTreeEquiv R S
      (canonicalBoundaryPrimal R S A)
      (rectangle 0 0 (R + 1) (S + 1) \
        Boundary.canonicalBoundary R S A))
    (hInterior : ∀ i, VacancyDeletionTreeEquiv R S
      (canonicalInteriorPrimal R S A i)
      (rectangle 0 0 (R + 1) (S + 1) \
        Boundary.canonicalInterior R S A i)) :
    CanonicalForestEvents A R S :=
  canonicalForestEventsOfDeletionComplementLawsAndRestriction
    R S A hRectangle (canonicalGlobalForestRestrictionLaw R S A)
    hWhole hBoundary hInterior

/-- The consolidated canonical deletion-equivalence family constructs all
forest events on a nondegenerate rectangle. -/
noncomputable def CanonicalVacancyDeletionTreeEquivs.canonicalForestEvents
    {A : Finset Point} {R S : ℕ}
    (d : CanonicalVacancyDeletionTreeEquivs A R S)
    (hR : 1 ≤ R) (hS : 1 ≤ S) :
    CanonicalForestEvents A R S :=
  canonicalForestEventsOfDeletionComplementLaws R S A
    (canonicalRectangleTreeComplementLaw hR hS)
    d.whole d.boundary d.interior

/-- A bounded face in the support of the full selected dual graph for an
interior component lies in the bounded face-star support. -/
theorem mem_boundedDualGraph_support_of_mem_dualEdgeGraph_support_some
    (R S : ℕ) (A : Finset Point)
    (i : Fin (Boundary.canonicalInteriorCount R S A))
    (f : BoundedFace (R + 1) (S + 1))
    (hf : some f ∈
      (dualEdgeGraph (canonicalInteriorPrimal R S A i)).support) :
    f ∈ (boundedDualGraph (canonicalInteriorPrimal R S A i)).support := by
  rw [SimpleGraph.mem_support] at hf ⊢
  rcases hf with ⟨v, hfv⟩
  cases v with
  | none =>
      exact False.elim
        (dualEdgeGraph_not_adj_none_of_not_perimeter
          (fun _ hp => canonicalInteriorPrimal_not_perimeter hp)
          (some f) hfv.symm)
  | some g => exact ⟨g, hfv⟩

/-- The simple graph selected by the ambient labels of a face-star tree is
exactly that tree mapped into the rectangular dual.  Vertices outside the
bounded-face image are isolated. -/
theorem simpleGraphOn_ambientBlockOfFaceStarTree
    {R S : ℕ} {A : Finset Point}
    {i : Fin (Boundary.canonicalInteriorCount R S A)}
    (T : InteriorFaceStarTree R S A i) :
    (rectangleDual (R + 1) (S + 1)).simpleGraphOn
        (ambientBlockOfFaceStarTree T :
          Set (RectangleEdge (R + 1) (S + 1))) =
      T.1.map (boundedDualCoreToDualVertex
        (canonicalInteriorPrimal R S A i)) := by
  let G := rectangleDual (R + 1) (S + 1)
  let emb := boundedDualCoreToDualVertex
    (canonicalInteriorPrimal R S A i)
  ext u v
  constructor
  · rintro ⟨huv, e, he, hlink⟩
    obtain ⟨p, rfl⟩ := (mem_ambientBlockOfFaceStarTree T e).mp he
    induction hp : p.1 using Sym2.inductionOn with
    | _ a b =>
        have hab : T.1.Adj a b := by
          rw [← SimpleGraph.mem_edgeSet, ← hp]
          exact p.2
        have hpairs : s(emb a, emb b) = s(u, v) := by
          rw [← hlink, ambientLabelOfFaceStarEdge_ends T p, hp,
            Sym2.map_mk]
        rcases Sym2.eq_iff.mp hpairs with h | h
        · exact ⟨huv, a, b, hab, h.1, h.2⟩
        · exact ⟨huv, b, a, hab.symm, h.2, h.1⟩
  · rintro ⟨huv, a, b, hab, ha, hb⟩
    let p : T.1.edgeSet := ⟨s(a, b), hab⟩
    refine ⟨huv, ambientLabelOfFaceStarEdge T p, ?_, ?_⟩
    · exact (mem_ambientBlockOfFaceStarTree T _).mpr ⟨p, rfl⟩
    · change (rectangleDual (R + 1) (S + 1)).ends
          (ambientLabelOfFaceStarEdge T p) = s(u, v)
      rw [ambientLabelOfFaceStarEdge_ends T p]
      change s(emb a, emb b) = s(u, v)
      rw [ha, hb]

/-- Every explicit interior event block is a labelled forest of the ambient
rectangular dual. -/
theorem interiorEventBlock_isEdgeForest
    (R S : ℕ) (A : Finset Point)
    (i : Fin (Boundary.canonicalInteriorCount R S A))
    (j : Fin (interiorFaceStarTreeCount R S A i)) :
    (rectangleDual (R + 1) (S + 1)).IsEdgeForest
      (interiorEventBlock R S A i j) := by
  let G := rectangleDual (R + 1) (S + 1)
  let T := interiorFaceStarTreeAt R S A i j
  let emb := boundedDualCoreToDualVertex
    (canonicalInteriorPrimal R S A i)
  have hGconn : G.Connected := rectangleDual_connected_pos (by omega) (by omega)
  apply G.isEdgeForest_of_simpleGraphOn_isAcyclic hGconn
  · intro e he hloop
    obtain ⟨p, rfl⟩ := (mem_ambientBlockOfFaceStarTree T e).mp he
    apply T.1.not_isDiag_of_mem_edgeSet p.2
    apply (Sym2.isDiag_map emb.injective).mp
    rw [← ambientLabelOfFaceStarEdge_ends T p]
    exact hloop
  · intro e he d hd heq
    obtain ⟨p, rfl⟩ := (mem_ambientBlockOfFaceStarTree T e).mp he
    obtain ⟨q, rfl⟩ := (mem_ambientBlockOfFaceStarTree T d).mp hd
    apply congrArg (ambientLabelOfFaceStarEdge T)
    apply Subtype.ext
    apply Sym2.map.injective emb.injective
    rw [← ambientLabelOfFaceStarEdge_ends T p,
      ← ambientLabelOfFaceStarEdge_ends T q]
    exact heq
  · change ((rectangleDual (R + 1) (S + 1)).simpleGraphOn
        (ambientBlockOfFaceStarTree T :
          Set (RectangleEdge (R + 1) (S + 1)))).IsAcyclic
    rw [simpleGraphOn_ambientBlockOfFaceStarTree T]
    exact SimpleGraph.IsAcyclic.map_embedding T.2.2.isAcyclic emb

/-- Every enumerated face-star tree block spans exactly the same contraction
components as all labels incident with that interior vacancy component. -/
theorem interiorEventBlock_reachable_eq_vacancyDualEdges
    (R S : ℕ) (A : Finset Point)
    (i : Fin (Boundary.canonicalInteriorCount R S A))
    (j : Fin (interiorFaceStarTreeCount R S A i)) :
    ((rectangleDual (R + 1) (S + 1)).simpleGraphOn
      (interiorEventBlock R S A i j :
        Set (RectangleEdge (R + 1) (S + 1)))).Reachable =
    ((rectangleDual (R + 1) (S + 1)).simpleGraphOn
      (vacancyDualEdges (canonicalInteriorPrimal R S A i) :
        Set (RectangleEdge (R + 1) (S + 1)))).Reachable := by
  let X := canonicalInteriorPrimal R S A i
  let G := rectangleDual (R + 1) (S + 1)
  let B := interiorEventBlock R S A i j
  let T := interiorFaceStarTreeAt R S A i j
  let emb := boundedDualCoreToDualVertex X
  let K := G.simpleGraphOn (B : Set (RectangleEdge (R + 1) (S + 1)))
  let H := G.simpleGraphOn
    (vacancyDualEdges X : Set (RectangleEdge (R + 1) (S + 1)))
  apply funext
  intro u
  apply funext
  intro v
  apply propext
  constructor
  · intro huv
    apply huv.mono
    exact G.simpleGraphOn_mono
      (interiorEventBlock_subset_vacancyDualEdges R S A i j)
  · intro huv
    cases u with
    | none =>
        cases v with
        | none => rfl
        | some g =>
            exact False.elim
              (SimpleGraph.not_reachable_of_neighborSet_left_eq_empty
                (by simp) (canonicalInterior_dualEdgeGraph_neighborSet_none
                  R S A i) huv)
    | some f =>
        cases v with
        | none =>
            exact False.elim
              (SimpleGraph.not_reachable_of_neighborSet_right_eq_empty
                (by simp) (canonicalInterior_dualEdgeGraph_neighborSet_none
                  R S A i) huv)
        | some g =>
            by_cases hfg : f = g
            · subst g
              rfl
            · have hsome : (some f : RectangleDualVertex (R + 1) (S + 1)) ≠
                  some g := fun h => hfg (Option.some.inj h)
              have hfH : some f ∈
                  (dualEdgeGraph X).support :=
                (SimpleGraph.mem_support _).mpr
                  (huv.nonempty_neighborSet_left hsome)
              have hgH : some g ∈
                  (dualEdgeGraph X).support :=
                (SimpleGraph.mem_support _).mpr
                  (huv.nonempty_neighborSet_right hsome)
              have hf : f ∈ (boundedDualGraph X).support :=
                mem_boundedDualGraph_support_of_mem_dualEdgeGraph_support_some
                  R S A i f hfH
              have hg : g ∈ (boundedDualGraph X).support :=
                mem_boundedDualGraph_support_of_mem_dualEdgeGraph_support_some
                  R S A i g hgH
              let f' : {z // z ∈ (boundedDualGraph X).support} := ⟨f, hf⟩
              let g' : {z // z ∈ (boundedDualGraph X).support} := ⟨g, hg⟩
              have hTreach : T.1.Reachable f' g' :=
                T.2.2.connected.preconnected f' g'
              let φ : T.1 →g K := {
                toFun := emb
                map_rel' := by
                  intro a b hab
                  have hab' : (K.comap emb).Adj a b := by
                    change (((rectangleDual (R + 1) (S + 1)).simpleGraphOn
                      (ambientBlockOfFaceStarTree T :
                        Set (RectangleEdge (R + 1) (S + 1)))).comap
                          (boundedDualCoreToDualVertex
                            (canonicalInteriorPrimal R S A i))).Adj a b
                    rw [ambientBlockOfFaceStarTree_comap T]
                    exact hab
                  exact hab'
              }
              exact hTreach.map φ

/-- The explicit face-star event family needs no additional forest or
component-spanning input: both facts follow from the rectangular geometry. -/
theorem interiorPlanarDualityInputOfDeletionComplementLaws
    (R S : ℕ) (A : Finset Point)
    (i : Fin (Boundary.canonicalInteriorCount R S A))
    (hRectangle : RectangleTreeComplementLaw (R + 1) (S + 1))
    (hDeletion : VacancyDeletionTreeEquiv R S
      (canonicalInteriorPrimal R S A i)
      (rectangle 0 0 (R + 1) (S + 1) \
        Boundary.canonicalInterior R S A i)) :
    InteriorPlanarDualityInput A R S i :=
  interiorPlanarDualityInputOfDeletionComplementLawsAndForestReach
    R S A i hRectangle hDeletion
    (interiorEventBlock_isEdgeForest R S A i)
    (interiorEventBlock_reachable_eq_vacancyDualEdges R S A i)

/-- For a nondegenerate rectangle, a single interior deletion equivalence is
the only remaining input for its complete planar-duality event family. -/
theorem interiorPlanarDualityInputOfVacancyDeletionTreeEquiv
    (R S : ℕ) (A : Finset Point)
    (hR : 1 ≤ R) (hS : 1 ≤ S)
    (i : Fin (Boundary.canonicalInteriorCount R S A))
    (hDeletion : VacancyDeletionTreeEquiv R S
      (canonicalInteriorPrimal R S A i)
      (rectangle 0 0 (R + 1) (S + 1) \
        Boundary.canonicalInterior R S A i)) :
    InteriorPlanarDualityInput A R S i :=
  interiorPlanarDualityInputOfDeletionComplementLaws R S A i
    (canonicalRectangleTreeComplementLaw hR hS) hDeletion

/-- The same consolidated deletion family supplies each interior
planar-duality input. -/
theorem CanonicalVacancyDeletionTreeEquivs.interiorPlanarDuality
    {A : Finset Point} {R S : ℕ}
    (d : CanonicalVacancyDeletionTreeEquivs A R S)
    (hR : 1 ≤ R) (hS : 1 ≤ S)
    (i : Fin (Boundary.canonicalInteriorCount R S A)) :
    InteriorPlanarDualityInput A R S i :=
  interiorPlanarDualityInputOfVacancyDeletionTreeEquiv
    R S A hR hS i (d.interior i)

end

end Dual

end SquareMaximality
