module

public import SquareMaximality.Dual.ForestEventsConstruction

@[expose] public section

/-!
# Deletion/contraction tree complements from full basis duality

This module proves the abstract graphic-matroid step needed by rectangular
vacancy deletion.  It derives the minor tree property from the already proved
full primal/dual tree-complement law, without a separate Euler-rank input.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace SquareMaximality

open Multigraph
open Multigraph.LabeledMultigraph

namespace Multigraph.LabeledMultigraph

variable {V E : Type*} [Fintype V] [Fintype E]

omit [Fintype E] in
/- The canonical labelled spanning forest of a connected selected subgraph
is itself a labelled spanning tree. -/
theorem spanningForestLabels_isSpanningTree_of_connected
    (G : LabeledMultigraph V E) (X : Finset E)
    (hX : (G.simpleGraphOn (X : Set E)).Connected) :
    G.IsSpanningTree (G.spanningForestLabels X) := by
  classical
  let F := G.spanningForestLabels X
  have hTconn : (G.spanningForestSubgraph X).Connected := by
    letI : Nonempty V := hX.nonempty
    refine { preconnected := ?_ }
    intro u v
    rw [G.spanningForestSubgraph_reachable_eq X]
    exact hX.preconnected u v
  have hTtree : (G.spanningForestSubgraph X).IsTree :=
    ⟨hTconn, G.spanningForestSubgraph_isAcyclic X⟩
  refine ⟨?_, ?_, ?_⟩
  · intro e heF hloop
    obtain ⟨p, rfl⟩ := (G.mem_spanningForestLabels X e).mp heF
    apply (G.spanningForestSubgraph X).not_isDiag_of_mem_edgeSet p.2
    rw [← G.spanningForestLabel_ends X p]
    exact hloop
  · rw [G.simpleGraphOn_spanningForestLabels X]
    exact hTconn
  · letI : Fintype (G.spanningForestSubgraph X).edgeSet := Fintype.ofFinite _
    change F.card + 1 = Fintype.card V
    have hcard : F.card =
        Fintype.card (G.spanningForestSubgraph X).edgeSet := by
      dsimp only [F, LabeledMultigraph.spanningForestLabels]
      rw [Finset.card_image_of_injective]
      · simp
      · exact G.spanningForestLabel_injective X
    rw [hcard, ← SimpleGraph.edgeFinset_card]
    exact hTtree.card_edgeFinset

end Multigraph.LabeledMultigraph

namespace Dual

noncomputable section

/-- A full ambient primal tree extending `F` may add only labels in `D`.
For a spanning tree of the graph obtained by deleting `D`, this is exactly
the usual maximality property. -/
def TreeExtensionOnlyThrough
    {V E : Type*} [Fintype V] [DecidableEq E]
    (G : LabeledMultigraph V E) (F D : Finset E) : Prop :=
  ∀ T, G.IsSpanningTree T → F ⊆ T → T ⊆ F ∪ D

/-- If every label outside `D` has its endpoints already connected by `F`,
then no ambient tree extending `F` can use a further label outside `D`.
Global uniqueness of endpoint labels rules out a parallel copy of the same
tree edge. -/
theorem treeExtensionOnlyThrough_of_reachable
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq E]
    (G : LabeledMultigraph V E)
    (hends : Function.Injective G.ends)
    (F D : Finset E)
    (hreach : ∀ e, e ∉ D → ∀ u v, G.IsLink e u v →
      (G.simpleGraphOn (F : Set E)).Reachable u v) :
    TreeExtensionOnlyThrough G F D := by
  classical
  intro T hT hFT e heT
  by_cases heF : e ∈ F
  · exact Finset.mem_union_left D heF
  by_cases heD : e ∈ D
  · exact Finset.mem_union_right F heD
  exfalso
  induction hlink : G.ends e using Sym2.inductionOn with
  | _ u v =>
      have huv : u ≠ v := by
        intro huv
        subst v
        apply hT.loopless heT
        change (G.ends e).IsDiag
        rw [hlink]
        exact Sym2.diag_isDiag _
      let K := G.simpleGraphOn (T : Set E)
      have hadjT : K.Adj u v := ⟨huv, e, heT, hlink⟩
      have hle : G.simpleGraphOn (F : Set E) ≤
          K.deleteEdges {s(u, v)} := by
        intro x y hxy
        rw [SimpleGraph.deleteEdges_adj]
        refine ⟨G.simpleGraphOn_mono hFT hxy, ?_⟩
        simp only [Set.mem_singleton_iff]
        intro hpair
        obtain ⟨_, f, hfF, hflink⟩ := hxy
        have hendsEq : G.ends f = G.ends e := by
          calc
            G.ends f = s(x, y) := hflink
            _ = s(u, v) := hpair
            _ = G.ends e := hlink.symm
        exact heF (hends hendsEq ▸ hfF)
      have hbridge : K.IsBridge s(u, v) :=
        (SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mp
          hT.toSimpleGraph_isTree.isAcyclic) hadjT
      exact (SimpleGraph.isBridge_iff.mp hbridge)
        ((hreach e heD u v hlink).mono hle)

/-- Abstract forward minor-basis theorem.  Suppose complementary full edge
sets exchange primal and dual spanning trees.  If `F` is maximal away from
the contracted labels `D`, then its connected contracted-dual complement is
already a tree; no Euler cardinality hypothesis is needed. -/
theorem contractedComplementEdges_isSpanningTree_of_fullComplement
    {VG VH E : Type*} [Fintype VG] [Fintype VH] [Fintype E]
    [DecidableEq E]
    (G : LabeledMultigraph VG E) (H : LabeledMultigraph VH E)
    (hHloop : ∀ e, ¬ H.IsLoop e)
    (hHconn : H.Connected)
    (hComplement : ∀ T : Finset E,
      G.IsSpanningTree T ↔
        H.IsSpanningTree (Finset.univ \ T))
    (D F : Finset E) (hFD : Disjoint F D)
    (hmax : TreeExtensionOnlyThrough G F D)
    (hconnected :
      ((H.contract D).simpleGraphOn
        (contractedComplementEdges H D F :
          Set (H.contractWithLoops D).NonLoopEdge)).Connected) :
    @LabeledMultigraph.IsSpanningTree
      (H.simpleGraphOn (D : Set E)).ConnectedComponent
      (H.contractWithLoops D).NonLoopEdge (H.contract D)
      (H.contractionComponentFintype D)
      (contractedComplementEdges H D F) := by
  classical
  letI : Fintype (H.simpleGraphOn (D : Set E)).ConnectedComponent :=
    H.contractionComponentFintype D
  letI : Fintype (H.contractWithLoops D).NonLoopEdge := Fintype.ofFinite _
  let S := contractedComplementEdges H D F
  let U := (H.contract D).spanningForestLabels S
  have hUtree : (H.contract D).IsSpanningTree U :=
    (H.contract D).spanningForestLabels_isSpanningTree_of_connected S
      hconnected
  have hUSub : U ⊆ S := (H.contract D).spanningForestLabels_subset S
  have hSU : S ⊆ U := by
    intro e heS
    by_contra heU
    let D₀ := H.spanningForestLabels D
    have hD₀forest : H.IsEdgeForest D₀ :=
      H.spanningForestLabels_isEdgeForest hHconn D
    have hD₀D : D₀ ⊆ D := H.spanningForestLabels_subset D
    have hReach :
        (H.simpleGraphOn (D₀ : Set E)).Reachable =
          (H.simpleGraphOn (D : Set E)).Reachable :=
      H.spanningForestLabels_reachable_eq D
    letI : Fintype (H.simpleGraphOn (D₀ : Set E)).ConnectedComponent :=
      H.contractionComponentFintype D₀
    letI : Fintype (H.contractWithLoops D₀).NonLoopEdge := Fintype.ofFinite _
    let φ := ContractionRelabel.contractSpanningTreeEquivOfReachableEq
      H D₀ D hReach
    let U₀ : (H.contract D₀).SpanningTree :=
      φ.symm ⟨U, hUtree⟩
    let Q₀ : {T : H.SpanningTree // D₀ ⊆ T.1} :=
      (H.contractionSpanningTreeEquiv hD₀forest).symm U₀
    let Q : H.SpanningTree := Q₀.1
    have hQval : Q.1 = H.liftContractTreeEdges D₀ U₀.1 := by
      rfl
    let P : Finset E := Finset.univ \ Q.1
    have hPtree : G.IsSpanningTree P := by
      apply (hComplement P).mpr
      simpa [P] using Q.2
    have hFP : F ⊆ P := by
      intro f hfF
      simp only [P, Finset.mem_sdiff, Finset.mem_univ, true_and]
      intro hfQ
      rw [hQval] at hfQ
      rcases (H.mem_liftContractTreeEdges D₀ U₀.1 f).mp hfQ with
        hfD₀ | ⟨q, hqU₀, hqf⟩
      · exact Finset.disjoint_left.mp hFD hfF (hD₀D hfD₀)
      · let q' := ContractionRelabel.contractionEdgeEquivOfReachableEq
            H D₀ D hReach q
        have hq'U : q' ∈ U := by
          have hEq : φ U₀ = (⟨U, hUtree⟩ : (H.contract D).SpanningTree) :=
            φ.apply_symm_apply ⟨U, hUtree⟩
          have hval : (φ U₀).1 = U := congrArg Subtype.val hEq
          change q' ∈ U
          rw [← hval]
          change q' ∈
            (ContractionRelabel.contractIsoOfReachableEq H D₀ D hReach).mapFinset
              U₀.1
          exact Finset.mem_map.mpr ⟨q, hqU₀, rfl⟩
        have hqval : q'.1 = f := by
          exact (ContractionRelabel.contractionEdgeEquivOfReachableEq_val
            H D₀ D hReach q).trans hqf
        have hqS : q' ∈ S := hUSub hq'U
        have hqNotF := (mem_contractedComplementEdges H D F q').mp hqS
        exact hqNotF (hqval ▸ hfF)
    have heNotD : e.1 ∉ D := by
      intro heD
      exact e.2 (H.contractWithLoops_isLoop_of_mem heD (hHloop e.1))
    have heNotF : e.1 ∉ F :=
      (mem_contractedComplementEdges H D F e).mp heS
    have heP : e.1 ∈ P := by
      simp only [P, Finset.mem_sdiff, Finset.mem_univ, true_and]
      intro heQ
      rw [hQval] at heQ
      rcases (H.mem_liftContractTreeEdges D₀ U₀.1 e.1).mp heQ with
        heD₀ | ⟨q, hqU₀, hqe⟩
      · exact heNotD (hD₀D heD₀)
      · let q' := ContractionRelabel.contractionEdgeEquivOfReachableEq
            H D₀ D hReach q
        have hq'U : q' ∈ U := by
          have hEq : φ U₀ = (⟨U, hUtree⟩ : (H.contract D).SpanningTree) :=
            φ.apply_symm_apply ⟨U, hUtree⟩
          have hval : (φ U₀).1 = U := congrArg Subtype.val hEq
          change q' ∈ U
          rw [← hval]
          change q' ∈
            (ContractionRelabel.contractIsoOfReachableEq H D₀ D hReach).mapFinset
              U₀.1
          exact Finset.mem_map.mpr ⟨q, hqU₀, rfl⟩
        have hqval : q'.1 = e.1 := by
          exact (ContractionRelabel.contractionEdgeEquivOfReachableEq_val
            H D₀ D hReach q).trans hqe
        have hq'e : q' = e := Subtype.ext hqval
        exact heU (hq'e ▸ hq'U)
    have heUnion : e.1 ∈ F ∪ D := hmax P hPtree hFP heP
    exact (Finset.mem_union.mp heUnion).elim heNotF heNotD
  have hSUeq : S = U := Finset.Subset.antisymm hSU hUSub
  simpa only [S, hSUeq] using hUtree

/-- Any uncontracted primal label which collapses to a loop in the dual
minor is forced into every maximal retained primal tree.  This is the label
bookkeeping needed for injectivity of deletion/cotree complementation. -/
theorem mem_of_contractWithLoops_isLoop_of_fullComplement
    {VG VH E : Type*} [Fintype VG] [Fintype VH] [Fintype E]
    [DecidableEq E]
    (G : LabeledMultigraph VG E) (H : LabeledMultigraph VH E)
    (hHconn : H.Connected)
    (hComplement : ∀ T : Finset E,
      G.IsSpanningTree T ↔
        H.IsSpanningTree (Finset.univ \ T))
    (D F : Finset E) (hFD : Disjoint F D)
    (hmax : TreeExtensionOnlyThrough G F D)
    (hTree :
      @LabeledMultigraph.IsSpanningTree
        (H.simpleGraphOn (D : Set E)).ConnectedComponent
        (H.contractWithLoops D).NonLoopEdge (H.contract D)
        (H.contractionComponentFintype D)
        (contractedComplementEdges H D F))
    {e : E} (heD : e ∉ D)
    (heLoop : (H.contractWithLoops D).IsLoop e) :
    e ∈ F := by
  classical
  let D₀ := H.spanningForestLabels D
  have hD₀forest : H.IsEdgeForest D₀ :=
    H.spanningForestLabels_isEdgeForest hHconn D
  have hD₀D : D₀ ⊆ D := H.spanningForestLabels_subset D
  have hReach :
      (H.simpleGraphOn (D₀ : Set E)).Reachable =
        (H.simpleGraphOn (D : Set E)).Reachable :=
    H.spanningForestLabels_reachable_eq D
  letI : Fintype (H.simpleGraphOn (D : Set E)).ConnectedComponent :=
    H.contractionComponentFintype D
  letI : Fintype (H.simpleGraphOn (D₀ : Set E)).ConnectedComponent :=
    H.contractionComponentFintype D₀
  letI : Fintype (H.contractWithLoops D).NonLoopEdge := Fintype.ofFinite _
  letI : Fintype (H.contractWithLoops D₀).NonLoopEdge := Fintype.ofFinite _
  let φ := ContractionRelabel.contractSpanningTreeEquivOfReachableEq
    H D₀ D hReach
  let S : (H.contract D).SpanningTree :=
    ⟨contractedComplementEdges H D F, hTree⟩
  let S₀ : (H.contract D₀).SpanningTree := φ.symm S
  let Q₀ : {T : H.SpanningTree // D₀ ⊆ T.1} :=
    (H.contractionSpanningTreeEquiv hD₀forest).symm S₀
  let Q : H.SpanningTree := Q₀.1
  have hQval : Q.1 = H.liftContractTreeEdges D₀ S₀.1 := by
    rfl
  let P : Finset E := Finset.univ \ Q.1
  have hPtree : G.IsSpanningTree P := by
    apply (hComplement P).mpr
    simpa [P] using Q.2
  have hFP : F ⊆ P := by
    intro f hfF
    simp only [P, Finset.mem_sdiff, Finset.mem_univ, true_and]
    intro hfQ
    rw [hQval] at hfQ
    rcases (H.mem_liftContractTreeEdges D₀ S₀.1 f).mp hfQ with
      hfD₀ | ⟨q, hqS₀, hqf⟩
    · exact Finset.disjoint_left.mp hFD hfF (hD₀D hfD₀)
    · let q' := ContractionRelabel.contractionEdgeEquivOfReachableEq
          H D₀ D hReach q
      have hq'S : q' ∈ S.1 := by
        have hEq : φ S₀ = S := φ.apply_symm_apply S
        have hval : (φ S₀).1 = S.1 := congrArg Subtype.val hEq
        rw [← hval]
        change q' ∈
          (ContractionRelabel.contractIsoOfReachableEq H D₀ D hReach).mapFinset
            S₀.1
        exact Finset.mem_map.mpr ⟨q, hqS₀, rfl⟩
      have hqval : q'.1 = f :=
        (ContractionRelabel.contractionEdgeEquivOfReachableEq_val
          H D₀ D hReach q).trans hqf
      have hqNotF :=
        (mem_contractedComplementEdges H D F q').mp hq'S
      exact hqNotF (hqval ▸ hfF)
  have heP : e ∈ P := by
    simp only [P, Finset.mem_sdiff, Finset.mem_univ, true_and]
    intro heQ
    rw [hQval] at heQ
    rcases (H.mem_liftContractTreeEdges D₀ S₀.1 e).mp heQ with
      heD₀ | ⟨q, hqS₀, hqe⟩
    · exact heD (hD₀D heD₀)
    · let q' := ContractionRelabel.contractionEdgeEquivOfReachableEq
          H D₀ D hReach q
      have hqval : q'.1 = e :=
        (ContractionRelabel.contractionEdgeEquivOfReachableEq_val
          H D₀ D hReach q).trans hqe
      exact q'.2 (hqval ▸ heLoop)
  rcases Finset.mem_union.mp (hmax P hPtree hFP heP) with heF | heD'
  · exact heF
  · exact False.elim (heD heD')

/-! ## Rectangular vacancy-deletion specialization -/

/-- Ambient primal labels selected by a tree of an arbitrary retained
integer-coordinate subgrid. -/
noncomputable def vacancyPrimalTreeLabels
    {R S : ℕ} {D : Finset Point}
    (hD : D ⊆ rectangle 0 0 (R + 1) (S + 1))
    (T : SimpleSpanningTreeType (inducedGrid D)) :
    Finset (RectangleEdge (R + 1) (S + 1)) :=
  labelsOfSimpleSubgraph (rectanglePrimal (R + 1) (S + 1))
    (T.1.map (vacancyDeletionToPrimal hD))

/-- Recovering labels after embedding a retained tree gives exactly its
mapped simple graph. -/
theorem simpleGraphOn_vacancyPrimalTreeLabels
    {R S : ℕ} {D : Finset Point}
    (hD : D ⊆ rectangle 0 0 (R + 1) (S + 1))
    (T : SimpleSpanningTreeType (inducedGrid D)) :
    (rectanglePrimal (R + 1) (S + 1)).simpleGraphOn
        (vacancyPrimalTreeLabels hD T :
          Set (RectangleEdge (R + 1) (S + 1))) =
      T.1.map (vacancyDeletionToPrimal hD) := by
  apply simpleGraphOn_labelsOfSimpleSubgraph
  intro u v huv
  rw [SimpleGraph.map_adj] at huv
  rcases huv with ⟨p, q, hpq, rfl, rfl⟩
  exact (vacancyDeletionPrimalGraphEmbedding hD).toHom.map_adj
    (T.2.1 hpq)

/-- Embedded labels of a retained-grid tree are acyclic in the full primal
rectangle. -/
theorem vacancyPrimalTreeLabels_isAcyclic
    {R S : ℕ} {D : Finset Point}
    (hD : D ⊆ rectangle 0 0 (R + 1) (S + 1))
    (T : SimpleSpanningTreeType (inducedGrid D)) :
    ((rectanglePrimal (R + 1) (S + 1)).simpleGraphOn
      (vacancyPrimalTreeLabels hD T :
        Set (RectangleEdge (R + 1) (S + 1)))).IsAcyclic := by
  rw [simpleGraphOn_vacancyPrimalTreeLabels]
  exact SimpleGraph.IsAcyclic.map_embedding T.2.2.isAcyclic
    (vacancyDeletionToPrimal hD)

/-- A retained vertex never belongs to the displayed deleted set. -/
theorem vacancyDeletionToPrimal_not_mem
    {R S : ℕ} {X : Finset (Fin (R + 1) × Fin (S + 1))}
    {D : Finset Point}
    (hD : D ⊆ rectangle 0 0 (R + 1) (S + 1))
    (hdelete : ∀ p : Fin (R + 1) × Fin (S + 1),
      p ∈ X ↔ Boundary.ofNatPoint (finPoint p) ∉ D)
    (p : {p : Point // p ∈ D}) :
    vacancyDeletionToPrimal hD p ∉ X := by
  intro hpX
  have hpNotD := (hdelete (vacancyDeletionToPrimal hD p)).mp hpX
  apply hpNotD
  rw [ofNatPoint_finPoint_vacancyDeletionToPrimal]
  exact p.2

/-- Primal tree labels retained after vertex deletion are disjoint from all
dual labels contracted around the deleted vertices. -/
theorem vacancyPrimalTreeLabels_disjoint_vacancyDualEdges
    {R S : ℕ} {X : Finset (Fin (R + 1) × Fin (S + 1))}
    {D : Finset Point}
    (hD : D ⊆ rectangle 0 0 (R + 1) (S + 1))
    (hdelete : ∀ p : Fin (R + 1) × Fin (S + 1),
      p ∈ X ↔ Boundary.ofNatPoint (finPoint p) ∉ D)
    (T : SimpleSpanningTreeType (inducedGrid D)) :
    Disjoint (vacancyPrimalTreeLabels hD T) (vacancyDualEdges X) := by
  classical
  apply Finset.disjoint_left.mpr
  intro e heT heD
  have heEdge := (mem_labelsOfSimpleSubgraph
    (rectanglePrimal (R + 1) (S + 1))
    (T.1.map (vacancyDeletionToPrimal hD)) e).mp heT
  induction hends : (rectanglePrimal (R + 1) (S + 1)).ends e using
      Sym2.inductionOn with
  | _ u v =>
      have huvMap : (T.1.map (vacancyDeletionToPrimal hD)).Adj u v := by
        rw [← SimpleGraph.mem_edgeSet, ← hends]
        exact heEdge
      rw [SimpleGraph.map_adj] at huvMap
      rcases huvMap with ⟨p, q, hpq, rfl, rfl⟩
      rw [mem_vacancyDualEdges] at heD
      rcases heD with ⟨x, hxX, hxe⟩
      have hxEnds := (primalIncident_iff_mem_rectanglePrimal_ends x e).mp hxe
      rw [hends, Sym2.mem_iff] at hxEnds
      rcases hxEnds with hx | hx
      · subst x
        exact vacancyDeletionToPrimal_not_mem hD hdelete p hxX
      · subst x
        exact vacancyDeletionToPrimal_not_mem hD hdelete q hxX

/-- Every ambient primal label surviving the vacancy deletion has its two
endpoints connected by the embedded retained tree. -/
theorem vacancyPrimalTreeLabels_reachable_of_not_mem
    {R S : ℕ} {X : Finset (Fin (R + 1) × Fin (S + 1))}
    {D : Finset Point}
    (hD : D ⊆ rectangle 0 0 (R + 1) (S + 1))
    (hdelete : ∀ p : Fin (R + 1) × Fin (S + 1),
      p ∈ X ↔ Boundary.ofNatPoint (finPoint p) ∉ D)
    (T : SimpleSpanningTreeType (inducedGrid D))
    (e : RectangleEdge (R + 1) (S + 1))
    (heD : e ∉ vacancyDualEdges X)
    (u v : Fin (R + 1) × Fin (S + 1))
    (hlink : (rectanglePrimal (R + 1) (S + 1)).IsLink e u v) :
    ((rectanglePrimal (R + 1) (S + 1)).simpleGraphOn
      (vacancyPrimalTreeLabels hD T :
        Set (RectangleEdge (R + 1) (S + 1)))).Reachable u v := by
  have huX : u ∉ X := by
    intro hu
    apply heD
    apply mem_vacancyDualEdges.mpr
    refine ⟨u, hu, ?_⟩
    apply (primalIncident_iff_mem_rectanglePrimal_ends u e).mpr
    rw [hlink]
    exact Sym2.mem_mk_left u v
  have hvX : v ∉ X := by
    intro hv
    apply heD
    apply mem_vacancyDualEdges.mpr
    refine ⟨v, hv, ?_⟩
    apply (primalIncident_iff_mem_rectanglePrimal_ends v e).mpr
    rw [hlink]
    exact Sym2.mem_mk_right u v
  let pu := vacancyRemainingToDeletion hD hdelete u huX
  let pv := vacancyRemainingToDeletion hD hdelete v hvX
  have hpupv : T.1.Reachable pu pv := T.2.2.connected.preconnected pu pv
  have hmapped : (T.1.map (vacancyDeletionToPrimal hD)).Reachable
      (vacancyDeletionToPrimal hD pu)
      (vacancyDeletionToPrimal hD pv) :=
    hpupv.map (SimpleGraph.Embedding.map
      (vacancyDeletionToPrimal hD) T.1).toHom
  rw [vacancyDeletionToPrimal_remainingToDeletion,
    vacancyDeletionToPrimal_remainingToDeletion] at hmapped
  rw [simpleGraphOn_vacancyPrimalTreeLabels]
  exact hmapped

/-- The generic contracted cotree obtained by complementing an embedded
retained primal tree. -/
noncomputable def vacancyContractedCotree
    {R S : ℕ} {X : Finset (Fin (R + 1) × Fin (S + 1))}
    {D : Finset Point}
    (hD : D ⊆ rectangle 0 0 (R + 1) (S + 1))
    (T : SimpleSpanningTreeType (inducedGrid D)) :
    Finset ((rectangleDual (R + 1) (S + 1)).contractWithLoops
      (vacancyDualEdges X)).NonLoopEdge :=
  contractedComplementEdges (rectangleDual (R + 1) (S + 1))
    (vacancyDualEdges X) (vacancyPrimalTreeLabels hD T)

@[simp] theorem mem_vacancyContractedCotree
    {R S : ℕ} {X : Finset (Fin (R + 1) × Fin (S + 1))}
    {D : Finset Point}
    (hD : D ⊆ rectangle 0 0 (R + 1) (S + 1))
    (T : SimpleSpanningTreeType (inducedGrid D))
    (e : ((rectangleDual (R + 1) (S + 1)).contractWithLoops
      (vacancyDualEdges X)).NonLoopEdge) :
    e ∈ vacancyContractedCotree hD T ↔
      e.1 ∉ vacancyPrimalTreeLabels hD T := by
  exact mem_contractedComplementEdges _ _ _ _

/-- Full rectangle tree complementation upgrades the connected generic
cotree to a contracted-dual spanning tree.  The proof uses only maximality
of the retained primal tree, not an Euler-rank identity. -/
theorem vacancyContractedCotree_isSpanningTree
    {R S : ℕ} (hR : 1 ≤ R) (hS : 1 ≤ S)
    {X : Finset (Fin (R + 1) × Fin (S + 1))}
    {D : Finset Point}
    (hD : D ⊆ rectangle 0 0 (R + 1) (S + 1))
    (hdelete : ∀ p : Fin (R + 1) × Fin (S + 1),
      p ∈ X ↔ Boundary.ofNatPoint (finPoint p) ∉ D)
    (T : SimpleSpanningTreeType (inducedGrid D)) :
    @LabeledMultigraph.IsSpanningTree
      ((rectangleDual (R + 1) (S + 1)).simpleGraphOn
        (vacancyDualEdges X :
          Set (RectangleEdge (R + 1) (S + 1)))).ConnectedComponent
      ((rectangleDual (R + 1) (S + 1)).contractWithLoops
        (vacancyDualEdges X)).NonLoopEdge
      ((rectangleDual (R + 1) (S + 1)).contract (vacancyDualEdges X))
      ((rectangleDual (R + 1) (S + 1)).contractionComponentFintype
        (vacancyDualEdges X))
      (vacancyContractedCotree hD T) := by
  let G := rectanglePrimal (R + 1) (S + 1)
  let H := rectangleDual (R + 1) (S + 1)
  let C := vacancyDualEdges X
  let F := vacancyPrimalTreeLabels hD T
  apply contractedComplementEdges_isSpanningTree_of_fullComplement
    G H
  · intro e
    exact rectangleDual_not_isLoop (by omega) (by omega) e
  · exact rectangleDual_connected (by omega) (by omega)
  · exact canonicalRectangleTreeComplementLaw hR hS
  · exact vacancyPrimalTreeLabels_disjoint_vacancyDualEdges
      hD hdelete T
  · apply treeExtensionOnlyThrough_of_reachable G
      (rectanglePrimal_ends_injective (R + 1) (S + 1))
    intro e heC u v huv
    exact vacancyPrimalTreeLabels_reachable_of_not_mem
      hD hdelete T e heC u v huv
  · exact contractedComplementEdges_connected_of_cutBoundaryEven
      G H rectanglePrimal_not_isLoop
      (rectanglePrimal_ends_injective (R + 1) (S + 1))
      (rectangleDual_connected (by omega) (by omega))
      (rectanglePrimal_dualCutBoundaryEven hR hS)
      C F (vacancyPrimalTreeLabels_isAcyclic hD T)

/-- The explicit forward deletion/cotree map, transported to the standard
finite instance used by the public contraction type. -/
noncomputable def vacancyDeletionCotreeMap
    {R S : ℕ} (hR : 1 ≤ R) (hS : 1 ≤ S)
    {X : Finset (Fin (R + 1) × Fin (S + 1))}
    {D : Finset Point}
    (hD : D ⊆ rectangle 0 0 (R + 1) (S + 1))
    (hdelete : ∀ p : Fin (R + 1) × Fin (S + 1),
      p ∈ X ↔ Boundary.ofNatPoint (finPoint p) ∉ D)
    (T : SimpleSpanningTreeType (inducedGrid D)) :
    ((rectangleDual (R + 1) (S + 1)).contract
      (vacancyDualEdges X)).SpanningTree := by
  let H := rectangleDual (R + 1) (S + 1)
  let C := vacancyDualEdges X
  let raw : @LabeledMultigraph.SpanningTree
      (H.simpleGraphOn (C : Set (RectangleEdge (R + 1) (S + 1)))).ConnectedComponent
      (H.contractWithLoops C).NonLoopEdge (H.contract C)
      (H.contractionComponentFintype C) inferInstance :=
    ⟨vacancyContractedCotree hD T,
      vacancyContractedCotree_isSpanningTree hR hS hD hdelete T⟩
  exact spanningTreeEquivOfFintype (H.contract C)
    (H.contractionComponentFintype C) inferInstance raw

@[simp] theorem vacancyDeletionCotreeMap_val
    {R S : ℕ} (hR : 1 ≤ R) (hS : 1 ≤ S)
    {X : Finset (Fin (R + 1) × Fin (S + 1))}
    {D : Finset Point}
    (hD : D ⊆ rectangle 0 0 (R + 1) (S + 1))
    (hdelete : ∀ p : Fin (R + 1) × Fin (S + 1),
      p ∈ X ↔ Boundary.ofNatPoint (finPoint p) ∉ D)
    (T : SimpleSpanningTreeType (inducedGrid D)) :
    (vacancyDeletionCotreeMap hR hS hD hdelete T).1 =
      vacancyContractedCotree hD T := by
  rfl

/-- Choose one retained-grid spanning tree inside the connected primal
complement of a contracted-dual tree. -/
noncomputable def vacancyPrimalComplementSpanningTree
    {R S : ℕ} (hR : 1 ≤ R) (hS : 1 ≤ S)
    {X : Finset (Fin (R + 1) × Fin (S + 1))}
    {D : Finset Point}
    (hD : D ⊆ rectangle 0 0 (R + 1) (S + 1))
    (hdelete : ∀ p : Fin (R + 1) × Fin (S + 1),
      p ∈ X ↔ Boundary.ofNatPoint (finPoint p) ∉ D)
    (hconn : (inducedGrid D).Connected)
    (T : ((rectangleDual (R + 1) (S + 1)).contract
      (vacancyDualEdges X)).SpanningTree) :
    SimpleSpanningTreeType (inducedGrid D) :=
  Classical.choose
    (exists_vacancyPrimalComplementSpanningTree
      hR hS hD hdelete hconn T)

theorem vacancyPrimalComplementSpanningTree_le
    {R S : ℕ} (hR : 1 ≤ R) (hS : 1 ≤ S)
    {X : Finset (Fin (R + 1) × Fin (S + 1))}
    {D : Finset Point}
    (hD : D ⊆ rectangle 0 0 (R + 1) (S + 1))
    (hdelete : ∀ p : Fin (R + 1) × Fin (S + 1),
      p ∈ X ↔ Boundary.ofNatPoint (finPoint p) ∉ D)
    (hconn : (inducedGrid D).Connected)
    (T : ((rectangleDual (R + 1) (S + 1)).contract
      (vacancyDualEdges X)).SpanningTree) :
    (vacancyPrimalComplementSpanningTree
      hR hS hD hdelete hconn T).1 ≤
      vacancyPrimalComplementGraph hR hS hD hdelete T :=
  Classical.choose_spec
    (exists_vacancyPrimalComplementSpanningTree
      hR hS hD hdelete hconn T)

/-- A contracted-dual tree label cannot also occur in any retained primal
tree chosen inside its complementary primal graph. -/
theorem not_mem_vacancyPrimalTreeLabels_of_le_complement
    {R S : ℕ} (hR : 1 ≤ R) (hS : 1 ≤ S)
    {X : Finset (Fin (R + 1) × Fin (S + 1))}
    {D : Finset Point}
    (hD : D ⊆ rectangle 0 0 (R + 1) (S + 1))
    (hdelete : ∀ p : Fin (R + 1) × Fin (S + 1),
      p ∈ X ↔ Boundary.ofNatPoint (finPoint p) ∉ D)
    (T : ((rectangleDual (R + 1) (S + 1)).contract
      (vacancyDualEdges X)).SpanningTree)
    (U : SimpleSpanningTreeType (inducedGrid D))
    (hU : U.1 ≤ vacancyPrimalComplementGraph hR hS hD hdelete T)
    (e : ((rectangleDual (R + 1) (S + 1)).contractWithLoops
      (vacancyDualEdges X)).NonLoopEdge)
    (heT : e ∈ T.1) :
    e.1 ∉ vacancyPrimalTreeLabels hD U := by
  intro heU
  have heMapped := (mem_labelsOfSimpleSubgraph
    (rectanglePrimal (R + 1) (S + 1))
    (U.1.map (vacancyDeletionToPrimal hD)) e.1).mp heU
  let p := vacancyContractedEdgeToDeletionEmbedding
    hR hS hD hdelete e
  have hmap : Sym2.map (vacancyDeletionToPrimal hD) p.1 =
      (rectanglePrimal (R + 1) (S + 1)).ends e.1 := by
    simpa [p, vacancyContractedEdgeToDeletionEmbedding] using
      (map_vacancyAvailableEdgeToDeletion hD hdelete
        (⟨e.1, vacancyContractedNonLoopEdge_not_mem hR hS X e⟩ :
          {q : RectangleEdge (R + 1) (S + 1) //
            q ∉ vacancyDualEdges X}))
  have hpU : p.1 ∈ U.1.edgeSet := by
    apply (SimpleGraph.Embedding.map
      (vacancyDeletionToPrimal hD) U.1).map_mem_edgeSet_iff.mp
    change Sym2.map (vacancyDeletionToPrimal hD) p.1 ∈
      (U.1.map (vacancyDeletionToPrimal hD)).edgeSet
    rw [hmap]
    exact heMapped
  have hpComp : p.1 ∈
      (vacancyPrimalComplementGraph hR hS hD hdelete T).edgeSet := by
    induction hp : p.1 using Sym2.inductionOn with
    | _ u v =>
        rw [hp] at hpU
        rw [SimpleGraph.mem_edgeSet] at hpU ⊢
        exact hU hpU
  have hpNotTree :=
    (mem_vacancyPrimalComplementGraph_edgeSet
      hR hS hD hdelete T p).mp hpComp
  apply hpNotTree
  rw [vacancyContractedTreeDeletionEdges, Finset.mem_map]
  exact ⟨e, heT, rfl⟩

/-- Choosing a spanning tree inside the primal complement and complementing
again returns the original contracted-dual tree. -/
theorem vacancyDeletionCotreeMap_primalComplementSpanningTree
    {R S : ℕ} (hR : 1 ≤ R) (hS : 1 ≤ S)
    {X : Finset (Fin (R + 1) × Fin (S + 1))}
    {D : Finset Point}
    (hD : D ⊆ rectangle 0 0 (R + 1) (S + 1))
    (hdelete : ∀ p : Fin (R + 1) × Fin (S + 1),
      p ∈ X ↔ Boundary.ofNatPoint (finPoint p) ∉ D)
    (hconn : (inducedGrid D).Connected)
    (T : ((rectangleDual (R + 1) (S + 1)).contract
      (vacancyDualEdges X)).SpanningTree) :
    vacancyDeletionCotreeMap hR hS hD hdelete
        (vacancyPrimalComplementSpanningTree
          hR hS hD hdelete hconn T) = T := by
  let U := vacancyPrimalComplementSpanningTree
    hR hS hD hdelete hconn T
  have hsub : T.1 ⊆
      (vacancyDeletionCotreeMap hR hS hD hdelete U).1 := by
    intro e heT
    rw [vacancyDeletionCotreeMap_val,
      mem_vacancyContractedCotree]
    exact not_mem_vacancyPrimalTreeLabels_of_le_complement
      hR hS hD hdelete T U
      (vacancyPrimalComplementSpanningTree_le
        hR hS hD hdelete hconn T) e heT
  apply Subtype.ext
  symm
  apply Finset.eq_of_subset_of_card_le hsub
  have hTcard := T.2.card_edges_add_one
  have hUcard := (vacancyDeletionCotreeMap
    hR hS hD hdelete U).2.card_edges_add_one
  omega

/-- Equality of explicit contracted cotrees determines inclusion of the
embedded retained primal labels.  Nonloop labels are visible directly;
labels collapsed by the contraction are forced into every retained tree. -/
theorem vacancyPrimalTreeLabels_subset_of_cotreeMap_eq
    {R S : ℕ} (hR : 1 ≤ R) (hS : 1 ≤ S)
    {X : Finset (Fin (R + 1) × Fin (S + 1))}
    {D : Finset Point}
    (hD : D ⊆ rectangle 0 0 (R + 1) (S + 1))
    (hdelete : ∀ p : Fin (R + 1) × Fin (S + 1),
      p ∈ X ↔ Boundary.ofNatPoint (finPoint p) ∉ D)
    (T U : SimpleSpanningTreeType (inducedGrid D))
    (hTU : vacancyDeletionCotreeMap hR hS hD hdelete T =
      vacancyDeletionCotreeMap hR hS hD hdelete U) :
    vacancyPrimalTreeLabels hD T ⊆ vacancyPrimalTreeLabels hD U := by
  intro e heT
  let G := rectanglePrimal (R + 1) (S + 1)
  let H := rectangleDual (R + 1) (S + 1)
  let C := vacancyDualEdges X
  have heNotC : e ∉ C := by
    exact fun heC => Finset.disjoint_left.mp
      (vacancyPrimalTreeLabels_disjoint_vacancyDualEdges
        hD hdelete T) heT heC
  by_cases heLoop : (H.contractWithLoops C).IsLoop e
  · apply mem_of_contractWithLoops_isLoop_of_fullComplement
      G H (rectangleDual_connected (by omega) (by omega))
      (canonicalRectangleTreeComplementLaw hR hS)
      C (vacancyPrimalTreeLabels hD U)
      (vacancyPrimalTreeLabels_disjoint_vacancyDualEdges
        hD hdelete U)
    · apply treeExtensionOnlyThrough_of_reachable G
        (rectanglePrimal_ends_injective (R + 1) (S + 1))
      intro f hfC u v huv
      exact vacancyPrimalTreeLabels_reachable_of_not_mem
        hD hdelete U f hfC u v huv
    · exact vacancyContractedCotree_isSpanningTree
        hR hS hD hdelete U
    · exact heNotC
    · exact heLoop
  · let q : (H.contractWithLoops C).NonLoopEdge := ⟨e, heLoop⟩
    have hqNotT : q ∉ vacancyContractedCotree hD T := by
      intro hqT
      exact (mem_vacancyContractedCotree hD T q).mp hqT heT
    by_contra heU
    have hqU : q ∈ vacancyContractedCotree hD U :=
      (mem_vacancyContractedCotree hD U q).mpr heU
    have hval := congrArg Subtype.val hTU
    rw [vacancyDeletionCotreeMap_val,
      vacancyDeletionCotreeMap_val] at hval
    exact hqNotT (hval.symm ▸ hqU)

/-- The explicit vacancy-deletion cotree map is injective. -/
theorem vacancyDeletionCotreeMap_injective
    {R S : ℕ} (hR : 1 ≤ R) (hS : 1 ≤ S)
    {X : Finset (Fin (R + 1) × Fin (S + 1))}
    {D : Finset Point}
    (hD : D ⊆ rectangle 0 0 (R + 1) (S + 1))
    (hdelete : ∀ p : Fin (R + 1) × Fin (S + 1),
      p ∈ X ↔ Boundary.ofNatPoint (finPoint p) ∉ D) :
    Function.Injective
      (vacancyDeletionCotreeMap hR hS hD hdelete) := by
  intro T U hTU
  have hlabels : vacancyPrimalTreeLabels hD T =
      vacancyPrimalTreeLabels hD U :=
    Finset.Subset.antisymm
      (vacancyPrimalTreeLabels_subset_of_cotreeMap_eq
        hR hS hD hdelete T U hTU)
      (vacancyPrimalTreeLabels_subset_of_cotreeMap_eq
        hR hS hD hdelete U T hTU.symm)
  apply Subtype.ext
  apply SimpleGraph.map_injective (vacancyDeletionToPrimal hD)
  rw [← simpleGraphOn_vacancyPrimalTreeLabels hD T,
    ← simpleGraphOn_vacancyPrimalTreeLabels hD U, hlabels]

/-- The generic graphic-matroid deletion/contraction equivalence for an
arbitrary rectangular vacancy set.  Its only geometric hypotheses say that
the displayed integer-coordinate deletion is the retained graph and is
connected.  No Euler-rank assumption is used. -/
noncomputable def vacancyDeletionTreeEquivOfCoordinateData
    {R S : ℕ} (hR : 1 ≤ R) (hS : 1 ≤ S)
    {X : Finset (Fin (R + 1) × Fin (S + 1))}
    {D : Finset Point}
    (hD : D ⊆ rectangle 0 0 (R + 1) (S + 1))
    (hdelete : ∀ p : Fin (R + 1) × Fin (S + 1),
      p ∈ X ↔ Boundary.ofNatPoint (finPoint p) ∉ D)
    (hconn : (inducedGrid D).Connected) :
    VacancyDeletionTreeEquiv R S X D :=
  Equiv.ofBijective
    (vacancyDeletionCotreeMap hR hS hD hdelete)
    ⟨vacancyDeletionCotreeMap_injective hR hS hD hdelete, by
      intro T
      refine ⟨vacancyPrimalComplementSpanningTree
        hR hS hD hdelete hconn T, ?_⟩
      exact vacancyDeletionCotreeMap_primalComplementSpanningTree
        hR hS hD hdelete hconn T⟩

end

end Dual
end SquareMaximality
