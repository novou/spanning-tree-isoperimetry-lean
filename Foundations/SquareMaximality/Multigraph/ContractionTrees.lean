import SquareMaximality.Multigraph.Contraction
import SquareMaximality.Multigraph.Events

/-!
# Spanning trees and finite edge contraction

This file proves the contraction identity directly at the level of labelled
edge sets.  No determinant or Matrix--Tree theorem is used.
-/

set_option autoImplicit false

namespace SquareMaximality.Multigraph
namespace LabeledMultigraph

variable {V E : Type*} (G : LabeledMultigraph V E)

noncomputable local instance contractionTreesDecidableEqEdge : DecidableEq E := Classical.decEq E
noncomputable local instance contractionTreesDecidableEqVertex : DecidableEq V := Classical.decEq V

/-- A contraction component has a finite type whenever the original vertex
type is finite.  This noncomputable instance avoids forcing clients to choose
a reachability decision procedure merely to state contraction identities. -/
noncomputable instance (priority := low) contractionComponentFintype
    [Finite V] (F : Finset E) :
    Fintype (G.simpleGraphOn (F : Set E)).ConnectedComponent :=
  Fintype.ofFinite _

/-- A selected edge label, bundled with its membership proof. -/
abbrev SelectedEdge (F : Finset E) := {e : E // e ∈ F}

/-- Send a selected nonloop label to its unordered pair of endpoints in the
underlying simple graph. -/
def selectedEndpoint (F : Finset E) (hloop : ∀ e ∈ F, ¬G.IsLoop e) :
    SelectedEdge F → (G.simpleGraphOn (F : Set E)).edgeSet := by
  intro e
  refine ⟨G.ends e.1, ?_⟩
  induction hends : G.ends e.1 using Sym2.inductionOn with
  | _ u v =>
      change (G.simpleGraphOn (F : Set E)).Adj u v
      have hlink : G.IsLink e.1 u v := hends
      refine ⟨?_, e.1, e.2, hlink⟩
      intro huv
      subst v
      exact hloop e.1 e.2 ((G.isLoop_iff_exists_isLoopAt e.1).mpr ⟨u, hlink⟩)

@[simp]
theorem selectedEndpoint_val (F : Finset E) (hloop : ∀ e ∈ F, ¬G.IsLoop e)
    (e : SelectedEdge F) :
    (G.selectedEndpoint F hloop e).1 = G.ends e.1 :=
  rfl

theorem selectedEndpoint_surjective (F : Finset E) (hloop : ∀ e ∈ F, ¬G.IsLoop e) :
    Function.Surjective (G.selectedEndpoint F hloop) := by
  rintro ⟨p, hp⟩
  induction p using Sym2.inductionOn with
  | _ u v =>
      have hadj : (G.simpleGraphOn (F : Set E)).Adj u v := by
        exact hp
      obtain ⟨_, e, heF, he⟩ := hadj
      refine ⟨⟨e, heF⟩, Subtype.ext ?_⟩
      exact he

/-- The underlying simple graph of a labelled spanning tree is a Mathlib
simple tree.  In particular, the cardinality definition of labelled trees
cannot hide a pair of parallel selected labels. -/
theorem IsSpanningTree.toSimpleGraph_isTree [Fintype V] [Finite E]
    {F : Finset E} (hF : G.IsSpanningTree F) :
    (G.simpleGraphOn (F : Set E)).IsTree := by
  rw [SimpleGraph.isTree_iff_connected_and_card]
  refine ⟨hF.selected_connected, ?_⟩
  have hsurj := G.selectedEndpoint_surjective F (fun _ he ↦ hF.loopless he)
  have hedge_le : Nat.card (G.simpleGraphOn (F : Set E)).edgeSet ≤ F.card := by
    calc
      Nat.card (G.simpleGraphOn (F : Set E)).edgeSet ≤ Nat.card (SelectedEdge F) :=
        Nat.card_le_card_of_surjective _ hsurj
      _ = F.card := Nat.card_eq_finsetCard F
  have hvert_le := hF.selected_connected.card_vert_le_card_edgeSet_add_one
  rw [show Nat.card V = Fintype.card V from Nat.card_eq_fintype_card] at hvert_le ⊢
  have hcard := hF.card_edges_add_one
  omega

/-- A spanning labelled tree has at most one selected label with any given
unordered pair of endpoints. -/
theorem IsSpanningTree.ends_injective [Fintype V] [Finite E]
    {F : Finset E} (hF : G.IsSpanningTree F) :
    Function.Injective (fun e : SelectedEdge F ↦ G.ends e.1) := by
  let f := G.selectedEndpoint F (fun _ he ↦ hF.loopless he)
  have hf_surj : Function.Surjective f := G.selectedEndpoint_surjective F _
  have hcard_domain : Nat.card (SelectedEdge F) = F.card := Nat.card_eq_finsetCard F
  have hcard_target : Nat.card (G.simpleGraphOn (F : Set E)).edgeSet = F.card := by
    have htree := hF.toSimpleGraph_isTree
    have hedge := (SimpleGraph.isTree_iff_connected_and_card.mp htree).2
    rw [show Nat.card V = Fintype.card V from Nat.card_eq_fintype_card] at hedge
    have hcard := hF.card_edges_add_one
    omega
  have hf_bij : Function.Bijective f :=
    (Nat.bijective_iff_surjective_and_card f).mpr
      ⟨hf_surj, hcard_domain.trans hcard_target.symm⟩
  intro e e' heq
  apply hf_bij.1
  apply Subtype.ext
  exact heq

/-- The labels of `T` that survive contraction of `F`. -/
noncomputable def contractTreeEdges (F T : Finset E) :
    Finset (G.contractWithLoops F).NonLoopEdge :=
  (G.contractWithLoops F).attachNonLoopEdges T

@[simp]
theorem mem_contractTreeEdges {F T : Finset E}
    (e : (G.contractWithLoops F).NonLoopEdge) :
    e ∈ G.contractTreeEdges F T ↔ e.1 ∈ T := by
  classical
  simp [contractTreeEdges, attachNonLoopEdges]

/-- In a spanning tree containing `F`, no unselected edge is accidentally
collapsed by contraction of `F`. -/
theorem IsSpanningTree.not_contractWithLoops_isLoop_of_mem_of_not_mem
    [Fintype V] [Finite E] {F T : Finset E}
    (hT : G.IsSpanningTree T) (hFT : F ⊆ T) {e : E}
    (heT : e ∈ T) (heF : e ∉ F) :
    ¬(G.contractWithLoops F).IsLoop e := by
  intro hcollapsed
  obtain ⟨u, v, hlink⟩ : ∃ u v, G.IsLink e u v := by
    induction hends : G.ends e using Sym2.inductionOn with
    | _ u v => exact ⟨u, v, hends⟩
  have huv : u ≠ v := by
    intro huv
    subst v
    exact hT.loopless heT ((G.isLoop_iff_exists_isLoopAt e).mpr ⟨u, hlink⟩)
  have hcomponent : G.contractionMap F u = G.contractionMap F v := by
    change (Sym2.map (G.contractionMap F) (G.ends e)).IsDiag at hcollapsed
    rw [hlink, Sym2.map_mk, Sym2.mk_isDiag_iff] at hcollapsed
    exact hcollapsed
  have hreachF : (G.simpleGraphOn (F : Set E)).Reachable u v :=
    SimpleGraph.ConnectedComponent.exact hcomponent
  let HT := G.simpleGraphOn (T : Set E)
  have hadjT : HT.Adj u v := ⟨huv, e, heT, hlink⟩
  have hle : G.simpleGraphOn (F : Set E) ≤ HT.deleteEdges {s(u, v)} := by
    intro x y hxy
    rw [SimpleGraph.deleteEdges_adj]
    refine ⟨G.simpleGraphOn_mono hFT hxy, ?_⟩
    simp only [Set.mem_singleton_iff]
    intro hpair
    obtain ⟨_, f, hfF, hflink⟩ := hxy
    have hfT : f ∈ T := hFT hfF
    have hends : G.ends f = G.ends e := by
      calc
        G.ends f = s(x, y) := hflink
        _ = s(u, v) := hpair
        _ = G.ends e := hlink.symm
    have hsub : (⟨f, hfT⟩ : SelectedEdge T) = ⟨e, heT⟩ :=
      IsSpanningTree.ends_injective G hT hends
    have hfe : f = e := congrArg Subtype.val hsub
    exact heF (hfe ▸ hfF)
  have hbridge : HT.IsBridge s(u, v) :=
    (SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mp hT.toSimpleGraph_isTree.isAcyclic) hadjT
  exact (SimpleGraph.isBridge_iff.mp hbridge) (hreachF.mono hle)

theorem IsSpanningTree.contractWithLoops_isLoop_iff_mem
    [Fintype V] [Finite E] {F T : Finset E}
    (hT : G.IsSpanningTree T) (hFT : F ⊆ T) {e : E} (heT : e ∈ T) :
    (G.contractWithLoops F).IsLoop e ↔ e ∈ F := by
  constructor
  · intro hcollapsed
    by_contra heF
    exact IsSpanningTree.not_contractWithLoops_isLoop_of_mem_of_not_mem
      G hT hFT heT heF hcollapsed
  · intro heF
    exact G.contractWithLoops_isLoop_of_mem heF (hT.loopless heT)

theorem IsSpanningTree.forget_contractTreeEdges [Fintype V] [Finite E]
    {F T : Finset E} (hT : G.IsSpanningTree T) (hFT : F ⊆ T) :
    (G.contractWithLoops F).forgetNonLoopEdges (G.contractTreeEdges F T) = T \ F := by
  classical
  ext e
  simp only [contractTreeEdges, forgetNonLoopEdges, attachNonLoopEdges,
    Finset.mem_map, Finset.mem_subtype, Finset.mem_sdiff]
  constructor
  · rintro ⟨e', he'T, heq⟩
    subst e
    exact ⟨he'T, fun heF ↦ e'.2
      ((IsSpanningTree.contractWithLoops_isLoop_iff_mem G hT hFT he'T).mpr heF)⟩
  · rintro ⟨heT, heF⟩
    have hsurvive : ¬(G.contractWithLoops F).IsLoop e :=
      (IsSpanningTree.contractWithLoops_isLoop_iff_mem G hT hFT heT).not.mpr heF
    exact ⟨⟨e, hsurvive⟩, heT, rfl⟩

theorem IsSpanningTree.card_contractTreeEdges [Fintype V] [Finite E]
    {F T : Finset E} (hT : G.IsSpanningTree T) (hFT : F ⊆ T) :
    (G.contractTreeEdges F T).card = T.card - F.card := by
  have h := congrArg Finset.card (IsSpanningTree.forget_contractTreeEdges G hT hFT)
  have hinter : F ∩ T = F := Finset.inter_eq_left.mpr hFT
  simpa [forgetNonLoopEdges, Finset.card_sdiff, hinter] using h

/-- One selected original-tree edge becomes either equality of contracted
components or a reachable contracted edge. -/
theorem IsSpanningTree.contractTreeEdges_reachable_of_adj
    [Fintype V] [Finite E] {F T : Finset E}
    {u v : V} (hadj : (G.simpleGraphOn (T : Set E)).Adj u v) :
    (G.contract F).simpleGraphOn (G.contractTreeEdges F T :
      Set (G.contractWithLoops F).NonLoopEdge) |>.Reachable
        (G.contractionMap F u) (G.contractionMap F v) := by
  obtain ⟨_, e, heT, hlink⟩ := hadj
  by_cases hcollapsed : (G.contractWithLoops F).IsLoop e
  · have hcomponent : G.contractionMap F u = G.contractionMap F v := by
      change (Sym2.map (G.contractionMap F) (G.ends e)).IsDiag at hcollapsed
      rw [hlink, Sym2.map_mk, Sym2.mk_isDiag_iff] at hcollapsed
      exact hcollapsed
    rw [hcomponent]
  · let e' : (G.contractWithLoops F).NonLoopEdge := ⟨e, hcollapsed⟩
    have hmapped : (G.contract F).IsLink e'
        (G.contractionMap F u) (G.contractionMap F v) := by
      exact G.mapVertices_isLink (G.contractionMap F) e u v hlink
    have hne : G.contractionMap F u ≠ G.contractionMap F v := by
      intro heq
      apply hcollapsed
      change (Sym2.map (G.contractionMap F) (G.ends e)).IsDiag
      rw [hlink, Sym2.map_mk, heq]
      exact Sym2.diag_isDiag _
    apply SimpleGraph.Adj.reachable
    exact ⟨hne, e', (G.mem_contractTreeEdges e').mpr heT, hmapped⟩

theorem IsSpanningTree.contractTreeEdges_connected
    [Fintype V] [Finite E] {F T : Finset E}
    (hT : G.IsSpanningTree T) :
    ((G.contract F).simpleGraphOn (G.contractTreeEdges F T :
      Set (G.contractWithLoops F).NonLoopEdge)).Connected := by
  let K := (G.contract F).simpleGraphOn (G.contractTreeEdges F T :
    Set (G.contractWithLoops F).NonLoopEdge)
  letI : Nonempty V := hT.vertex_nonempty
  refine { preconnected := ?_ }
  intro c d
  refine SimpleGraph.ConnectedComponent.ind₂ (fun u v ↦ ?_) c d
  have hr := hT.selected_connected.preconnected u v
  rw [SimpleGraph.reachable_iff_reflTransGen] at hr ⊢
  exact hr.lift' (G.contractionMap F) fun x y hxy ↦
    (SimpleGraph.reachable_iff_reflTransGen _ _).mp
      (IsSpanningTree.contractTreeEdges_reachable_of_adj G hxy)

/-- Lift contracted labels back to their original labels and adjoin the
contracted forest. -/
noncomputable def liftContractTreeEdges (F : Finset E)
    (S : Finset (G.contractWithLoops F).NonLoopEdge) : Finset E :=
  F ∪ (G.contractWithLoops F).forgetNonLoopEdges S

@[simp]
theorem mem_liftContractTreeEdges (F : Finset E)
    (S : Finset (G.contractWithLoops F).NonLoopEdge) (e : E) :
    e ∈ G.liftContractTreeEdges F S ↔
      e ∈ F ∨ ∃ e' ∈ S, e'.1 = e := by
  classical
  simp [liftContractTreeEdges, forgetNonLoopEdges]

/-- A chosen original representative of a contraction component. -/
noncomputable def contractionRep (F : Finset E)
    (c : (G.simpleGraphOn (F : Set E)).ConnectedComponent) : V :=
  c.out

@[simp]
theorem contractionMap_contractionRep (F : Finset E)
    (c : (G.simpleGraphOn (F : Set E)).ConnectedComponent) :
    G.contractionMap F (G.contractionRep F c) = c :=
  c.out_eq

theorem liftContractTreeEdges_reachable_of_same_component
    (F : Finset E) (S : Finset (G.contractWithLoops F).NonLoopEdge)
    {u v : V} (huv : G.contractionMap F u = G.contractionMap F v) :
    (G.simpleGraphOn (G.liftContractTreeEdges F S : Set E)).Reachable u v := by
  apply SimpleGraph.Reachable.mono
    (G.simpleGraphOn_mono (Finset.subset_union_left (s₂ :=
      (G.contractWithLoops F).forgetNonLoopEdges S)))
  exact SimpleGraph.ConnectedComponent.exact huv

/-- A contracted selected edge lifts to a path between the chosen original
representatives of its endpoint components. -/
theorem liftContractTreeEdges_reachable_of_adj
    (F : Finset E) (S : Finset (G.contractWithLoops F).NonLoopEdge)
    {c d : (G.simpleGraphOn (F : Set E)).ConnectedComponent}
    (hadj : ((G.contract F).simpleGraphOn (S :
      Set (G.contractWithLoops F).NonLoopEdge)).Adj c d) :
    (G.simpleGraphOn (G.liftContractTreeEdges F S : Set E)).Reachable
      (G.contractionRep F c) (G.contractionRep F d) := by
  obtain ⟨hcd, e', heS, hlinkContract⟩ := hadj
  let e : E := e'.1
  obtain ⟨x, y, hlink⟩ : ∃ x y, G.IsLink e x y := by
    induction hends : G.ends e using Sym2.inductionOn with
    | _ x y => exact ⟨x, y, hends⟩
  have hmapped : s(G.contractionMap F x, G.contractionMap F y) = s(c, d) := by
    change Sym2.map (G.contractionMap F) (G.ends e) = s(c, d) at hlinkContract
    rw [hlink, Sym2.map_mk] at hlinkContract
    exact hlinkContract
  have hxy : x ≠ y := by
    intro hxy
    subst y
    apply e'.2
    change (Sym2.map (G.contractionMap F) (G.ends e)).IsDiag
    rw [hlink, Sym2.map_mk]
    exact Sym2.diag_isDiag _
  have heLift : e ∈ G.liftContractTreeEdges F S := by
    exact (G.mem_liftContractTreeEdges F S e).mpr (Or.inr ⟨e', heS, rfl⟩)
  have hadjLift : (G.simpleGraphOn (G.liftContractTreeEdges F S : Set E)).Adj x y :=
    ⟨hxy, e, heLift, hlink⟩
  rcases Sym2.eq_iff.mp hmapped with h | h
  · have hcx : G.contractionMap F (G.contractionRep F c) = G.contractionMap F x := by
      rw [G.contractionMap_contractionRep]
      exact h.1.symm
    have hyd : G.contractionMap F y = G.contractionMap F (G.contractionRep F d) := by
      rw [G.contractionMap_contractionRep]
      exact h.2
    exact (G.liftContractTreeEdges_reachable_of_same_component F S hcx).trans
      (hadjLift.reachable.trans
        (G.liftContractTreeEdges_reachable_of_same_component F S hyd))
  · have hcy : G.contractionMap F (G.contractionRep F c) = G.contractionMap F y := by
      rw [G.contractionMap_contractionRep]
      exact h.2.symm
    have hxd : G.contractionMap F x = G.contractionMap F (G.contractionRep F d) := by
      rw [G.contractionMap_contractionRep]
      exact h.1
    exact (G.liftContractTreeEdges_reachable_of_same_component F S hcy).trans
      (hadjLift.symm.reachable.trans
        (G.liftContractTreeEdges_reachable_of_same_component F S hxd))

theorem liftContractTreeEdges_reachable
    (F : Finset E) (S : Finset (G.contractWithLoops F).NonLoopEdge)
    {c d : (G.simpleGraphOn (F : Set E)).ConnectedComponent}
    (hreach : ((G.contract F).simpleGraphOn (S :
      Set (G.contractWithLoops F).NonLoopEdge)).Reachable c d) :
    (G.simpleGraphOn (G.liftContractTreeEdges F S : Set E)).Reachable
      (G.contractionRep F c) (G.contractionRep F d) := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at hreach ⊢
  exact hreach.lift' (G.contractionRep F) fun c' d' hcd ↦
    (SimpleGraph.reachable_iff_reflTransGen _ _).mp
      (G.liftContractTreeEdges_reachable_of_adj F S hcd)

theorem IsSpanningTree.liftContractTreeEdges_connected
    [Fintype V] [Fintype E] {F : Finset E}
    {S : Finset (G.contractWithLoops F).NonLoopEdge}
    (hS : (G.contract F).IsSpanningTree S) :
    (G.simpleGraphOn (G.liftContractTreeEdges F S : Set E)).Connected := by
  let Q := (G.simpleGraphOn (F : Set E)).ConnectedComponent
  let H := G.simpleGraphOn (G.liftContractTreeEdges F S : Set E)
  let K := (G.contract F).simpleGraphOn (S : Set (G.contractWithLoops F).NonLoopEdge)
  letI : Nonempty Q := hS.vertex_nonempty
  letI : Nonempty V := Nonempty.map (G.contractionRep F) (inferInstance : Nonempty Q)
  refine { preconnected := ?_ }
  intro u v
  have hquot : K.Reachable (G.contractionMap F u) (G.contractionMap F v) :=
    hS.selected_connected.preconnected _ _
  have hrep : H.Reachable
      (G.contractionRep F (G.contractionMap F u))
      (G.contractionRep F (G.contractionMap F v)) := by
    exact G.liftContractTreeEdges_reachable F S hquot
  have hu : H.Reachable u (G.contractionRep F (G.contractionMap F u)) :=
    G.liftContractTreeEdges_reachable_of_same_component F S (by simp)
  have hv : H.Reachable (G.contractionRep F (G.contractionMap F v)) v :=
    G.liftContractTreeEdges_reachable_of_same_component F S (by simp)
  exact hu.trans (hrep.trans hv)

/-- Distinct surviving labels of an original tree remain distinct simple
edges after contraction. -/
theorem IsSpanningTree.contractTreeEdges_ends_injective
    [Fintype V] [Fintype E] {F T : Finset E}
    (hT : G.IsSpanningTree T) (hFT : F ⊆ T) :
    Function.Injective (fun e : SelectedEdge (G.contractTreeEdges F T) ↦
      (G.contract F).ends e.1) := by
  intro a b hab
  apply Subtype.ext
  apply Subtype.ext
  by_contra hne
  let e₁ : E := a.1.1
  let e₂ : E := b.1.1
  have he₁T : e₁ ∈ T := (G.mem_contractTreeEdges a.1).mp a.2
  have he₂T : e₂ ∈ T := (G.mem_contractTreeEdges b.1).mp b.2
  have he₁e₂ : e₁ ≠ e₂ := hne
  obtain ⟨u, v, hlink₁⟩ : ∃ u v, G.IsLink e₁ u v := by
    induction hends : G.ends e₁ using Sym2.inductionOn with
    | _ u v => exact ⟨u, v, hends⟩
  let c := G.contractionMap F u
  let d := G.contractionMap F v
  have hcd : c ≠ d := by
    intro hcd
    apply a.1.2
    change (Sym2.map (G.contractionMap F) (G.ends e₁)).IsDiag
    rw [hlink₁, Sym2.map_mk]
    change s(c, d).IsDiag
    rw [hcd]
    exact Sym2.diag_isDiag _
  have hlink₁c : (G.contract F).IsLink a.1 c d := by
    exact G.mapVertices_isLink (G.contractionMap F) e₁ u v hlink₁
  have hlink₂c : (G.contract F).IsLink b.1 c d := by
    change (G.contract F).ends b.1 = s(c, d)
    calc
      (G.contract F).ends b.1 = (G.contract F).ends a.1 := hab.symm
      _ = s(c, d) := hlink₁c
  let S₂ : Finset (G.contractWithLoops F).NonLoopEdge := {b.1}
  have hadj₂ : ((G.contract F).simpleGraphOn (S₂ :
      Set (G.contractWithLoops F).NonLoopEdge)).Adj c d :=
    ⟨hcd, b.1, by simp [S₂], hlink₂c⟩
  have hrepPath := G.liftContractTreeEdges_reachable_of_adj F S₂ hadj₂
  have hu : (G.simpleGraphOn (G.liftContractTreeEdges F S₂ : Set E)).Reachable
      u (G.contractionRep F c) :=
    G.liftContractTreeEdges_reachable_of_same_component F S₂ (by simp [c])
  have hv : (G.simpleGraphOn (G.liftContractTreeEdges F S₂ : Set E)).Reachable
      (G.contractionRep F d) v :=
    G.liftContractTreeEdges_reachable_of_same_component F S₂ (by simp [d])
  have hpath : (G.simpleGraphOn (G.liftContractTreeEdges F S₂ : Set E)).Reachable u v :=
    hu.trans (hrepPath.trans hv)
  have he₁F : e₁ ∉ F := by
    intro heF
    exact a.1.2 (G.contractWithLoops_isLoop_of_mem heF (hT.loopless he₁T))
  have he₁notLift : e₁ ∉ G.liftContractTreeEdges F S₂ := by
    intro heLift
    rcases (G.mem_liftContractTreeEdges F S₂ e₁).mp heLift with heF | ⟨e', he'S, he'e₁⟩
    · exact he₁F heF
    · have he'b : e' = b.1 := Finset.mem_singleton.mp (by simpa [S₂] using he'S)
      apply he₁e₂
      simpa [e₁, e₂, he'b] using he'e₁.symm
  let HT := G.simpleGraphOn (T : Set E)
  have hle : G.simpleGraphOn (G.liftContractTreeEdges F S₂ : Set E) ≤
      HT.deleteEdges {s(u, v)} := by
    intro x y hxy
    rw [SimpleGraph.deleteEdges_adj]
    obtain ⟨hxyne, f, hfLift, hflink⟩ := hxy
    have hfT : f ∈ T := by
      rcases (G.mem_liftContractTreeEdges F S₂ f).mp hfLift with hfF | ⟨e', he'S, he'f⟩
      · exact hFT hfF
      · have he'b : e' = b.1 := Finset.mem_singleton.mp (by simpa [S₂] using he'S)
        have hfe₂ : f = e₂ := by simpa [e₂, he'b] using he'f.symm
        exact hfe₂ ▸ he₂T
    refine ⟨⟨hxyne, f, hfT, hflink⟩, ?_⟩
    simp only [Set.mem_singleton_iff]
    intro hpair
    have hends : G.ends f = G.ends e₁ := by
      calc
        G.ends f = s(x, y) := hflink
        _ = s(u, v) := hpair
        _ = G.ends e₁ := hlink₁.symm
    have hsub : (⟨f, hfT⟩ : SelectedEdge T) = ⟨e₁, he₁T⟩ :=
      IsSpanningTree.ends_injective G hT hends
    have hfe₁ : f = e₁ := congrArg Subtype.val hsub
    exact he₁notLift (hfe₁ ▸ hfLift)
  have hadj₁T : HT.Adj u v := ⟨hcd.imp (fun huv ↦ by subst v; rfl), e₁, he₁T, hlink₁⟩
  have hbridge : HT.IsBridge s(u, v) :=
    (SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mp hT.toSimpleGraph_isTree.isAcyclic) hadj₁T
  exact (SimpleGraph.isBridge_iff.mp hbridge) (hpath.mono hle)

/-- Every simple edge left after contracting a subtree is a bridge. -/
theorem IsSpanningTree.contractTreeEdges_isBridge
    [Fintype V] [Fintype E] {F T : Finset E}
    (hT : G.IsSpanningTree T) (hFT : F ⊆ T)
    {c d : (G.simpleGraphOn (F : Set E)).ConnectedComponent}
    (hadj : ((G.contract F).simpleGraphOn (G.contractTreeEdges F T :
      Set (G.contractWithLoops F).NonLoopEdge)).Adj c d) :
    ((G.contract F).simpleGraphOn (G.contractTreeEdges F T :
      Set (G.contractWithLoops F).NonLoopEdge)).IsBridge s(c, d) := by
  let C := G.contractTreeEdges F T
  let K := (G.contract F).simpleGraphOn (C : Set (G.contractWithLoops F).NonLoopEdge)
  obtain ⟨hcd, e', he'C, hlinkContract⟩ := hadj
  let e : E := e'.1
  have heT : e ∈ T := (G.mem_contractTreeEdges e').mp he'C
  obtain ⟨u, v, hlink⟩ : ∃ u v, G.IsLink e u v := by
    induction hends : G.ends e using Sym2.inductionOn with
    | _ u v => exact ⟨u, v, hends⟩
  have huv : u ≠ v := by
    intro huv
    subst v
    exact hT.loopless heT ((G.isLoop_iff_exists_isLoopAt e).mpr ⟨u, hlink⟩)
  have hmapped : s(G.contractionMap F u, G.contractionMap F v) = s(c, d) := by
    change Sym2.map (G.contractionMap F) (G.ends e) = s(c, d) at hlinkContract
    rw [hlink, Sym2.map_mk] at hlinkContract
    exact hlinkContract
  have heF : e ∉ F := by
    intro heF
    exact e'.2 (G.contractWithLoops_isLoop_of_mem heF (hT.loopless heT))
  let C' := C.erase e'
  have hdelete : K.deleteEdges {s(c, d)} =
      (G.contract F).simpleGraphOn (C' : Set (G.contractWithLoops F).NonLoopEdge) := by
    ext x y
    constructor
    · intro hxy
      rw [SimpleGraph.deleteEdges_adj] at hxy
      obtain ⟨⟨hxyne, f, hfC, hflink⟩, hpair⟩ := hxy
      refine ⟨hxyne, f, ?_, hflink⟩
      apply Finset.mem_erase.mpr
      refine ⟨?_, hfC⟩
      intro hfe
      subst f
      apply hpair
      simp only [Set.mem_singleton_iff]
      calc
        s(x, y) = (G.contract F).ends e' := hflink.symm
        _ = s(c, d) := hlinkContract
    · rintro ⟨hxyne, f, hfC', hflink⟩
      rw [SimpleGraph.deleteEdges_adj]
      have hfC : f ∈ C := Finset.mem_of_mem_erase hfC'
      refine ⟨⟨hxyne, f, hfC, hflink⟩, ?_⟩
      simp only [Set.mem_singleton_iff]
      intro hpair
      have hends : (G.contract F).ends f = (G.contract F).ends e' := by
        calc
          (G.contract F).ends f = s(x, y) := hflink
          _ = s(c, d) := hpair
          _ = (G.contract F).ends e' := hlinkContract.symm
      have hsub : (⟨f, hfC⟩ : SelectedEdge C) = ⟨e', he'C⟩ :=
        IsSpanningTree.contractTreeEdges_ends_injective G hT hFT hends
      exact (Finset.ne_of_mem_erase hfC') (congrArg Subtype.val hsub)
  rw [SimpleGraph.isBridge_iff]
  intro hreachDelete
  have hreachC' : ((G.contract F).simpleGraphOn
      (C' : Set (G.contractWithLoops F).NonLoopEdge)).Reachable c d := by
    rw [← hdelete]
    exact hreachDelete
  have hrepPath := G.liftContractTreeEdges_reachable F C' hreachC'
  have hpath : (G.simpleGraphOn (G.liftContractTreeEdges F C' : Set E)).Reachable u v := by
    rcases Sym2.eq_iff.mp hmapped with h | h
    · have hu := G.liftContractTreeEdges_reachable_of_same_component F C'
          (u := u) (v := G.contractionRep F c) (by simp [h.1])
      have hv := G.liftContractTreeEdges_reachable_of_same_component F C'
          (u := G.contractionRep F d) (v := v) (by simp [h.2])
      exact hu.trans (hrepPath.trans hv)
    · have hu := G.liftContractTreeEdges_reachable_of_same_component F C'
          (u := u) (v := G.contractionRep F d) (by simp [h.1])
      have hv := G.liftContractTreeEdges_reachable_of_same_component F C'
          (u := G.contractionRep F c) (v := v) (by simp [h.2])
      exact hu.trans (hrepPath.symm.trans hv)
  have heNotLift : e ∉ G.liftContractTreeEdges F C' := by
    intro heLift
    rcases (G.mem_liftContractTreeEdges F C' e).mp heLift with heFin | ⟨f, hfC', hfe⟩
    · exact heF heFin
    · have hfe' : f = e' := Subtype.ext hfe
      exact (Finset.ne_of_mem_erase hfC') hfe'
  let HT := G.simpleGraphOn (T : Set E)
  have hle : G.simpleGraphOn (G.liftContractTreeEdges F C' : Set E) ≤
      HT.deleteEdges {s(u, v)} := by
    intro x y hxy
    rw [SimpleGraph.deleteEdges_adj]
    obtain ⟨hxyne, f, hfLift, hflink⟩ := hxy
    have hfT : f ∈ T := by
      rcases (G.mem_liftContractTreeEdges F C' f).mp hfLift with hfF | ⟨f', hf'C', hf'f⟩
      · exact hFT hfF
      · have hf'C : f' ∈ C := Finset.mem_of_mem_erase hf'C'
        have hf'T : f'.1 ∈ T := (G.mem_contractTreeEdges f').mp hf'C
        exact hf'f ▸ hf'T
    refine ⟨⟨hxyne, f, hfT, hflink⟩, ?_⟩
    simp only [Set.mem_singleton_iff]
    intro hpair
    have hends : G.ends f = G.ends e := by
      calc
        G.ends f = s(x, y) := hflink
        _ = s(u, v) := hpair
        _ = G.ends e := hlink.symm
    have hsub : (⟨f, hfT⟩ : SelectedEdge T) = ⟨e, heT⟩ :=
      IsSpanningTree.ends_injective G hT hends
    have hfe : f = e := congrArg Subtype.val hsub
    exact heNotLift (hfe ▸ hfLift)
  have hadjT : HT.Adj u v := ⟨huv, e, heT, hlink⟩
  have hbridgeT : HT.IsBridge s(u, v) :=
    (SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mp hT.toSimpleGraph_isTree.isAcyclic) hadjT
  exact (SimpleGraph.isBridge_iff.mp hbridgeT) (hpath.mono hle)

theorem IsSpanningTree.contractTreeEdges_simpleGraph_isTree
    [Fintype V] [Fintype E] {F T : Finset E}
    (hT : G.IsSpanningTree T) (hFT : F ⊆ T) :
    ((G.contract F).simpleGraphOn (G.contractTreeEdges F T :
      Set (G.contractWithLoops F).NonLoopEdge)).IsTree := by
  refine ⟨IsSpanningTree.contractTreeEdges_connected G hT, ?_⟩
  rw [SimpleGraph.isAcyclic_iff_forall_adj_isBridge]
  exact fun _ _ hadj ↦ IsSpanningTree.contractTreeEdges_isBridge G hT hFT hadj

/-- Contracting a contained forest in a labelled spanning tree produces a
labelled spanning tree of the contraction. -/
theorem IsSpanningTree.contractTreeEdges_isSpanningTree
    [Fintype V] [Fintype E] {F T : Finset E}
    (hT : G.IsSpanningTree T) (hFT : F ⊆ T) :
    (G.contract F).IsSpanningTree (G.contractTreeEdges F T) := by
  let C := G.contractTreeEdges F T
  let K := (G.contract F).simpleGraphOn (C : Set (G.contractWithLoops F).NonLoopEdge)
  refine ⟨?_, IsSpanningTree.contractTreeEdges_connected G hT, ?_⟩
  · intro e _
    exact e.2
  · have htree : K.IsTree :=
      IsSpanningTree.contractTreeEdges_simpleGraph_isTree G hT hFT
    let endpoint := (G.contract F).selectedEndpoint C (fun e _ ↦ e.2)
    have hsurj : Function.Surjective endpoint :=
      (G.contract F).selectedEndpoint_surjective C (fun e _ ↦ e.2)
    have hinj : Function.Injective endpoint := by
      intro e e' hee'
      apply IsSpanningTree.contractTreeEdges_ends_injective G hT hFT
      exact congrArg Subtype.val hee'
    have hcardEdges : Nat.card K.edgeSet = C.card := by
      calc
        Nat.card K.edgeSet = Nat.card (SelectedEdge C) :=
          (Nat.card_congr (Equiv.ofBijective endpoint ⟨hinj, hsurj⟩)).symm
        _ = C.card := Nat.card_eq_finsetCard C
    have htreeCard := (SimpleGraph.isTree_iff_connected_and_card.mp htree).2
    rw [hcardEdges,
      show Nat.card (G.simpleGraphOn (F : Set E)).ConnectedComponent =
        Fintype.card (G.simpleGraphOn (F : Set E)).ConnectedComponent
        from Nat.card_eq_fintype_card] at htreeCard
    exact htreeCard

/-- A forest has the expected component count.  The proof uses one extending
spanning tree and the preceding contraction construction. -/
theorem IsEdgeForest.card_add_components [Fintype V] [Fintype E]
    {F : Finset E} (hF : G.IsEdgeForest F) :
    F.card + Fintype.card (G.simpleGraphOn (F : Set E)).ConnectedComponent =
      Fintype.card V := by
  obtain ⟨T, hFT⟩ := hF
  have hcontract := IsSpanningTree.contractTreeEdges_isSpanningTree G T.2 hFT
  have hcontractCard := hcontract.card_edges_add_one
  have hsurvivorCard := IsSpanningTree.card_contractTreeEdges G T.2 hFT
  have htreeCard := T.2.card_edges_add_one
  have hFcard : F.card ≤ T.1.card := Finset.card_le_card hFT
  omega

/-- Lifting a contracted spanning tree and adjoining the forest gives an
original spanning tree. -/
theorem IsEdgeForest.liftContractTreeEdges_isSpanningTree
    [Fintype V] [Fintype E] {F : Finset E}
    (hF : G.IsEdgeForest F)
    {S : Finset (G.contractWithLoops F).NonLoopEdge}
    (hS : (G.contract F).IsSpanningTree S) :
    G.IsSpanningTree (G.liftContractTreeEdges F S) := by
  obtain ⟨T, hFT⟩ := hF
  have hloopF : ∀ e ∈ F, ¬G.IsLoop e := fun _ he ↦ T.2.loopless (hFT he)
  refine ⟨?_, IsSpanningTree.liftContractTreeEdges_connected G hS, ?_⟩
  · intro e heLift
    rcases (G.mem_liftContractTreeEdges F S e).mp heLift with heF | ⟨e', heS, he'e⟩
    · exact hloopF e heF
    · subst e
      intro hloop
      apply e'.2
      obtain ⟨x, hx⟩ := (G.isLoop_iff_exists_isLoopAt e'.1).mp hloop
      change (Sym2.map (G.contractionMap F) (G.ends e'.1)).IsDiag
      rw [hx, Sym2.map_mk]
      exact Sym2.diag_isDiag _
  · have hdisj : Disjoint F ((G.contractWithLoops F).forgetNonLoopEdges S) := by
      rw [Finset.disjoint_left]
      intro e heF heForget
      obtain ⟨e', heS, he'e⟩ := Finset.mem_map.mp heForget
      subst e
      exact e'.2 (G.contractWithLoops_isLoop_of_mem heF (hloopF e'.1 heF))
    have hforgetCard : ((G.contractWithLoops F).forgetNonLoopEdges S).card = S.card := by
      simp [forgetNonLoopEdges]
    have hcomponentCard := IsEdgeForest.card_add_components G ⟨T, hFT⟩
    have hSCard := hS.card_edges_add_one
    rw [liftContractTreeEdges, Finset.card_union_of_disjoint hdisj, hforgetCard]
    omega

@[simp]
theorem IsSpanningTree.lift_contractTreeEdges [Fintype V] [Fintype E]
    {F T : Finset E} (hT : G.IsSpanningTree T) (hFT : F ⊆ T) :
    G.liftContractTreeEdges F (G.contractTreeEdges F T) = T := by
  rw [liftContractTreeEdges, IsSpanningTree.forget_contractTreeEdges G hT hFT]
  exact Finset.union_sdiff_of_subset hFT

@[simp]
theorem IsEdgeForest.contract_liftContractTreeEdges [Fintype V] [Fintype E]
    {F : Finset E} (hF : G.IsEdgeForest F)
    (S : Finset (G.contractWithLoops F).NonLoopEdge) :
    G.contractTreeEdges F (G.liftContractTreeEdges F S) = S := by
  obtain ⟨T, hFT⟩ := hF
  have hloopF : ∀ e ∈ F, ¬G.IsLoop e := fun _ he ↦ T.2.loopless (hFT he)
  ext e
  rw [G.mem_contractTreeEdges]
  constructor
  · intro heLift
    rcases (G.mem_liftContractTreeEdges F S e.1).mp heLift with heF | ⟨e', heS, he'e⟩
    · exact False.elim (e.2 (G.contractWithLoops_isLoop_of_mem heF (hloopF e.1 heF)))
    · have he'eq : e' = e := Subtype.ext he'e
      exact he'eq ▸ heS
  · intro heS
    exact (G.mem_liftContractTreeEdges F S e.1).mpr (Or.inr ⟨e, heS, rfl⟩)

/-- The direct finite equivalence behind the contraction identity. -/
noncomputable def contractionSpanningTreeEquiv [Fintype V] [Fintype E]
    {F : Finset E} (hF : G.IsEdgeForest F) :
    {T : G.SpanningTree // F ⊆ T.1} ≃ (G.contract F).SpanningTree where
  toFun T := ⟨G.contractTreeEdges F T.1.1,
    IsSpanningTree.contractTreeEdges_isSpanningTree G T.1.2 T.2⟩
  invFun S := ⟨⟨G.liftContractTreeEdges F S.1,
    IsEdgeForest.liftContractTreeEdges_isSpanningTree G hF S.2⟩,
    Finset.subset_union_left⟩
  left_inv T := Subtype.ext (Subtype.ext
    (IsSpanningTree.lift_contractTreeEdges G T.1.2 T.2))
  right_inv S := Subtype.ext (IsEdgeForest.contract_liftContractTreeEdges G hF S.1)

theorem containmentCount_eq_natCard [Fintype V] [Fintype E] (F : Finset E) :
    G.containmentCount F = Nat.card {T : G.SpanningTree // F ⊆ T.1} := by
  classical
  rw [containmentCount]
  exact (Nat.subtype_card (G.spanningTreesContaining F) (by
    intro T
    simp [spanningTreesContaining, spanningTrees])).symm

/-- Finite contraction identity for a forest event. -/
theorem containmentCount_eq_spanningTreeCount_contract
    [Fintype V] [Fintype E] {F : Finset E} (hF : G.IsEdgeForest F) :
    G.containmentCount F = (G.contract F).spanningTreeCount := by
  calc
    G.containmentCount F = Nat.card {T : G.SpanningTree // F ⊆ T.1} :=
      G.containmentCount_eq_natCard F
    _ = Nat.card (G.contract F).SpanningTree :=
      Nat.card_congr (G.contractionSpanningTreeEquiv hF)
    _ = (G.contract F).spanningTreeCount := rfl

/-- The corresponding uniform-spanning-tree probability ratio identity. -/
theorem containmentRatio_eq_contract_ratio
    [Fintype V] [Fintype E] {F : Finset E} (hF : G.IsEdgeForest F) :
    G.containmentRatio F =
      ((G.contract F).spanningTreeCount : ℝ) / (G.spanningTreeCount : ℝ) := by
  rw [containmentRatio, G.containmentCount_eq_spanningTreeCount_contract hF]

end LabeledMultigraph
end SquareMaximality.Multigraph
