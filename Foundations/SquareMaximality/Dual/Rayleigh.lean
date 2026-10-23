module

public import SquareMaximality.Dual.TappSeries
public import SquareMaximality.Dual.PlanarComplement
public import SquareMaximality.Inputs.MatrixTree
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.Analysis.Matrix.Order

@[expose] public section

set_option backward.privateInPublic true

/-!
# Finite Rayleigh monotonicity and the half-plane exhaustion boundary

This module isolates the finite electrical step in Tapp's Proposition 5.2.
The graph-specific input is an explicit all-minors Matrix--Tree cofactor
identity: the spanning-forest count is a reduced Laplacian determinant and
the separating two-forest count is the corresponding diagonal adjugate
entry.  Everything after that identity--positive definiteness, monotonicity
of Laplacian energy, and antitonicity of the inverse quadratic form--is
proved here.

The final section states a concrete finite half-plane exhaustion interface.
It deliberately asks only for the one-sided finite multiplier lower bound
used in Tapp's contradiction with square-lattice bulk entropy; it does not
postulate a resistance limit or the target `HalfPlaneTwoForestResistanceBound`.
-/

set_option autoImplicit false

namespace SquareMaximality
namespace Dual

open scoped BigOperators Matrix
open Multigraph Multigraph.LabeledMultigraph

universe u

/-! ## The exact all-minors Matrix--Tree boundary -/

/-! ### Simple graphs as uniquely edge-labelled multigraphs -/

/-- Regard every unordered edge of a finite simple graph as its own label.
This is the canonical bridge from the labelled Matrix--Tree interface to
Mathlib's simple-graph Laplacian. -/
def simpleEdgeLabeledGraph {V : Type*} (G : SimpleGraph V) :
    LabeledMultigraph V G.edgeSet where
  ends e := e.1

@[simp] theorem simpleEdgeLabeledGraph_ends
    {V : Type*} (G : SimpleGraph V) (e : G.edgeSet) :
    (simpleEdgeLabeledGraph G).ends e = e.1 := rfl

theorem simpleEdgeLabeledGraph_ends_injective
    {V : Type*} (G : SimpleGraph V) :
    Function.Injective (simpleEdgeLabeledGraph G).ends := by
  intro e f hef
  exact Subtype.ext hef

theorem simpleEdgeLabeledGraph_loopless
    {V : Type*} (G : SimpleGraph V) (e : G.edgeSet) :
    ¬(simpleEdgeLabeledGraph G).IsLoop e := by
  exact G.not_isDiag_of_mem_edgeSet e.2

@[simp] theorem simpleEdgeLabeledGraph_toSimpleGraph
    {V : Type*} (G : SimpleGraph V) :
    (simpleEdgeLabeledGraph G).toSimpleGraph = G := by
  ext u v
  constructor
  · rintro ⟨_hne, e, he⟩
    rw [← SimpleGraph.mem_edgeSet, ← he]
    exact e.2
  · intro huv
    refine ⟨huv.ne, ⟨s(u, v), (SimpleGraph.mem_edgeSet G).mpr huv⟩, rfl⟩

private theorem simpleEdgeLabeledGraph_edgeMultiplicity
    {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (u v : V) :
    (simpleEdgeLabeledGraph G).edgeMultiplicity u v =
      if G.Adj u v then 1 else 0 := by
  classical
  by_cases huv : G.Adj u v
  · let e₀ : (simpleEdgeLabeledGraph G).LinkEdge u v :=
      ⟨⟨s(u, v), (SimpleGraph.mem_edgeSet G).mpr huv⟩, rfl⟩
    letI : Unique ((simpleEdgeLabeledGraph G).LinkEdge u v) :=
      { default := e₀
        uniq := fun e ↦ by
          apply Subtype.ext
          apply Subtype.ext
          exact e.2 }
    rw [LabeledMultigraph.edgeMultiplicity, Nat.card_unique, if_pos huv]
  · letI : IsEmpty ((simpleEdgeLabeledGraph G).LinkEdge u v) :=
      ⟨fun e ↦ huv (by
        rw [← SimpleGraph.mem_edgeSet, ← e.2]
        exact e.1.2)⟩
    rw [LabeledMultigraph.edgeMultiplicity,
      Finite.card_eq_zero_iff.mpr inferInstance, if_neg huv]

private theorem simpleEdgeLabeledGraph_adjacencyMultiplicity
    {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (u v : V) :
    (simpleEdgeLabeledGraph G).adjacencyMultiplicity u v =
      if G.Adj u v then 1 else 0 := by
  classical
  by_cases huv : u = v
  · subst v
    simp
  · rw [(simpleEdgeLabeledGraph G).adjacencyMultiplicity_of_ne huv,
      simpleEdgeLabeledGraph_edgeMultiplicity]

private theorem simpleEdgeLabeledGraph_degree
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (u : V) :
    (simpleEdgeLabeledGraph G).degree u = G.degree u := by
  classical
  rw [LabeledMultigraph.degree]
  simp_rw [simpleEdgeLabeledGraph_adjacencyMultiplicity]
  exact (G.degree_eq_sum_if_adj (R := ℕ) u).symm

theorem simpleEdgeLabeledGraph_laplacian
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (simpleEdgeLabeledGraph G).laplacian ℤ = G.lapMatrix ℤ := by
  classical
  ext u v
  by_cases huv : u = v
  · subst v
    simp [SimpleGraph.lapMatrix, SimpleGraph.degMatrix,
      simpleEdgeLabeledGraph_degree]
  · simp [LabeledMultigraph.laplacian_apply, SimpleGraph.lapMatrix,
      SimpleGraph.degMatrix, huv,
      simpleEdgeLabeledGraph_adjacencyMultiplicity]

theorem simpleEdgeLabeledGraph_reducedLaplacian
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (root : V) :
    (simpleEdgeLabeledGraph G).reducedLaplacian ℤ root =
      reducedLapMatrix G root := by
  ext u v
  exact congr_fun (congr_fun (simpleEdgeLabeledGraph_laplacian G) u.1) v.1

/-- For a connected simple graph, its maximal-forest count is exactly the
labelled spanning-tree count of its canonical edge labelling. -/
theorem simpleEdgeLabeledGraph_spanningTreeCount
    {V : Type*} [Fintype V] (G : SimpleGraph V) (hG : G.Connected) :
    (simpleEdgeLabeledGraph G).spanningTreeCount = spanningForestCount G := by
  classical
  rw [spanningForestCount_eq_treeCount hG]
  unfold LabeledMultigraph.spanningTreeCount treeCount
  let e := labeledSpanningTreeEquivSimple (simpleEdgeLabeledGraph G)
    (simpleEdgeLabeledGraph_loopless G)
    (simpleEdgeLabeledGraph_ends_injective G)
  have hs : (simpleEdgeLabeledGraph G).toSimpleGraph = G :=
    simpleEdgeLabeledGraph_toSimpleGraph G
  rw [hs] at e
  exact Nat.card_congr e

/-- The root-reduced real Laplacian of a finite simple graph. -/
def rayleighReducedLaplacian
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (root : V) :
    Matrix {v : V // v ≠ root} {v : V // v ≠ root} ℝ :=
  reducedLapMatrix G root

private theorem map_simple_lapMatrix_int_real
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (Int.castRingHom ℝ).mapMatrix (G.lapMatrix ℤ) = G.lapMatrix ℝ := by
  ext u v
  simp [SimpleGraph.lapMatrix, SimpleGraph.degMatrix,
    Matrix.diagonal_apply]

private theorem det_reducedLapMatrix_cast
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (root : V) :
    (((reducedLapMatrix G root).det : ℤ) : ℝ) =
      (rayleighReducedLaplacian G root).det := by
  calc
    (((reducedLapMatrix G root).det : ℤ) : ℝ) =
        ((Int.castRingHom ℝ).mapMatrix (reducedLapMatrix G root)).det :=
      RingHom.map_det (Int.castRingHom ℝ) _
    _ = _ := by
      congr 1
      ext u v
      have hmap := congrArg
        (fun M : Matrix V V ℝ ↦ M u.1 v.1)
        (map_simple_lapMatrix_int_real G)
      exact hmap

/-- The ordinary cofactor half of the needed all-minors identity follows
directly from the labelled Matrix--Tree interface. -/
theorem spanningForestCount_eq_reducedLaplacian_det_of_matrixTree
    (hMatrixTree : LabeledMultigraphCofactorInput.{u, u})
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.Connected) (root : V) :
    (spanningForestCount G : ℝ) =
      (rayleighReducedLaplacian G root).det := by
  have hcount := simpleEdgeLabeledGraph_spanningTreeCount G hG
  have hcofactor := hMatrixTree V G.edgeSet
    (simpleEdgeLabeledGraph G) root
  rw [hcount, simpleEdgeLabeledGraph_reducedLaplacian] at hcofactor
  calc
    (spanningForestCount G : ℝ) =
        (((reducedLapMatrix G root).det : ℤ) : ℝ) := by
      exact_mod_cast hcofactor
    _ = _ := det_reducedLapMatrix_cast G root

/-! ### The added-edge form of the all-minors theorem -/

private theorem edge_le_of_adj'
    {V : Type*} {G : SimpleGraph V} {a b : V} (hab : G.Adj a b) :
    SimpleGraph.edge a b ≤ G :=
  (SimpleGraph.edge_le_iff G).mpr (Or.inr hab)

private theorem inf_edge_eq_bot_of_not_adj'
    {V : Type*} {G : SimpleGraph V} {a b : V}
    (hab : ¬G.Adj a b) :
    G ⊓ SimpleGraph.edge a b = ⊥ := by
  apply le_antisymm
  · intro u v huv
    rcases (SimpleGraph.edge_adj a b u v).mp huv.2 with
      ⟨⟨rfl, rfl⟩ | ⟨rfl, rfl⟩, _⟩
    · exact (hab huv.1).elim
    · exact (hab huv.1.symm).elim
  · exact bot_le

private theorem addedEdgeTree_reconstruct
    {V : Type*} {G : SimpleGraph V} {a b : V}
    (T : SimpleSpanningTreeType (G ⊔ SimpleGraph.edge a b))
    (hTab : T.1.Adj a b) :
    T.1 = (T.1 ⊓ G) ⊔ SimpleGraph.edge a b := by
  calc
    T.1 = T.1 ⊓ (G ⊔ SimpleGraph.edge a b) :=
      (inf_eq_left.mpr T.2.1).symm
    _ = (T.1 ⊓ G) ⊔ (T.1 ⊓ SimpleGraph.edge a b) := by
      simp only [inf_sup_left]
    _ = (T.1 ⊓ G) ⊔ SimpleGraph.edge a b := by
      rw [inf_eq_right.mpr (edge_le_of_adj' hTab)]

private noncomputable def addedEdgeTreeWithout_to_base
    {V : Type*} {G : SimpleGraph V} {a b : V}
    (T : SimpleSpanningTreeType (G ⊔ SimpleGraph.edge a b))
    (hTab : ¬T.1.Adj a b) : SimpleSpanningTreeType G := by
  refine ⟨T.1, ?_, T.2.2⟩
  intro u v huv
  rcases T.2.1 huv with hGuv | habuv
  · exact hGuv
  · rcases (SimpleGraph.edge_adj a b u v).mp habuv with
      ⟨⟨rfl, rfl⟩ | ⟨rfl, rfl⟩, _⟩
    · exact (hTab huv).elim
    · exact (hTab huv.symm).elim

private noncomputable def addedEdgeTreeWith_to_twoForest
    {V : Type*} [Fintype V] {G : SimpleGraph V} {a b : V}
    (hG : G.Connected) (hab : a ≠ b) (hnotadj : ¬G.Adj a b)
    (T : SimpleSpanningTreeType (G ⊔ SimpleGraph.edge a b))
    (hTab : T.1.Adj a b) : ABTwoForestType G a b := by
  let F := T.1 ⊓ G
  have hreconstruct : T.1 = F ⊔ SimpleGraph.edge a b :=
    addedEdgeTree_reconstruct T hTab
  have hFacyclic : F.IsAcyclic := T.2.2.isAcyclic.anti inf_le_left
  have hnreach : ¬F.Reachable a b := by
    have hcriterion := (SimpleGraph.isAcyclic_sup_fromEdgeSet_iff
      (G := F) (u := a) (v := b)).mp (hreconstruct ▸ T.2.2.isAcyclic)
    intro hreach
    rcases hcriterion.2 hreach with heq | hadj
    · exact hab heq
    · exact hnotadj hadj.2
  refine ⟨F, inf_le_right, hFacyclic, hnreach, ?_⟩
  rw [← hreconstruct]
  apply le_antisymm
  · exact fun u v _ ↦ hG u v
  · intro u v huv
    exact T.2.2.connected u v

private noncomputable def baseTree_to_addedEdgeTree
    {V : Type*} {G : SimpleGraph V} {a b : V}
    (T : SimpleSpanningTreeType G) :
    SimpleSpanningTreeType (G ⊔ SimpleGraph.edge a b) :=
  ⟨T.1, T.2.1.trans le_sup_left, T.2.2⟩

private noncomputable def twoForest_to_addedEdgeTree
    {V : Type*} [Fintype V] {G : SimpleGraph V} {a b : V}
    (hG : G.Connected) (_hab : a ≠ b)
    (F : ABTwoForestType G a b) :
    SimpleSpanningTreeType (G ⊔ SimpleGraph.edge a b) := by
  let T := F.1 ⊔ SimpleGraph.edge a b
  refine ⟨T, sup_le_sup F.2.1 le_rfl, ?_⟩
  constructor
  · letI : Nonempty V := hG.nonempty
    apply SimpleGraph.Connected.mk
    intro u v
    rw [F.2.2.2.2]
    exact hG u v
  · exact F.2.2.1.sup_edge_of_not_reachable F.2.2.2.1

private noncomputable def addedEdgeTreeToSum
    {V : Type*} [Fintype V] {G : SimpleGraph V} {a b : V}
    (hG : G.Connected) (hab : a ≠ b) (hnotadj : ¬G.Adj a b)
    (T : SimpleSpanningTreeType (G ⊔ SimpleGraph.edge a b)) :
    SimpleSpanningTreeType G ⊕ ABTwoForestType G a b := by
  classical
  exact if hTab : T.1.Adj a b then
    Sum.inr (addedEdgeTreeWith_to_twoForest hG hab hnotadj T hTab)
  else Sum.inl (addedEdgeTreeWithout_to_base T hTab)

private noncomputable def sumToAddedEdgeTree
    {V : Type*} [Fintype V] {G : SimpleGraph V} {a b : V}
    (hG : G.Connected) (hab : a ≠ b) :
    SimpleSpanningTreeType G ⊕ ABTwoForestType G a b →
      SimpleSpanningTreeType (G ⊔ SimpleGraph.edge a b)
  | Sum.inl T => baseTree_to_addedEdgeTree T
  | Sum.inr F => twoForest_to_addedEdgeTree hG hab F

private theorem addedEdgeTreeToSum_of_adj
    {V : Type*} [Fintype V] {G : SimpleGraph V} {a b : V}
    (hG : G.Connected) (hab : a ≠ b) (hnotadj : ¬G.Adj a b)
    (T : SimpleSpanningTreeType (G ⊔ SimpleGraph.edge a b))
    (hTab : T.1.Adj a b) :
    addedEdgeTreeToSum hG hab hnotadj T =
      Sum.inr (addedEdgeTreeWith_to_twoForest hG hab hnotadj T hTab) := by
  classical
  unfold addedEdgeTreeToSum
  rw [dif_pos hTab]

private theorem addedEdgeTreeToSum_of_not_adj
    {V : Type*} [Fintype V] {G : SimpleGraph V} {a b : V}
    (hG : G.Connected) (hab : a ≠ b) (hnotadj : ¬G.Adj a b)
    (T : SimpleSpanningTreeType (G ⊔ SimpleGraph.edge a b))
    (hTab : ¬T.1.Adj a b) :
    addedEdgeTreeToSum hG hab hnotadj T =
      Sum.inl (addedEdgeTreeWithout_to_base T hTab) := by
  classical
  unfold addedEdgeTreeToSum
  rw [dif_neg hTab]

@[simp] private theorem sumToAddedEdgeTree_inl
    {V : Type*} [Fintype V] {G : SimpleGraph V} {a b : V}
    (hG : G.Connected) (hab : a ≠ b) (T : SimpleSpanningTreeType G) :
    sumToAddedEdgeTree hG hab (Sum.inl T) = baseTree_to_addedEdgeTree T := rfl

@[simp] private theorem sumToAddedEdgeTree_inr
    {V : Type*} [Fintype V] {G : SimpleGraph V} {a b : V}
    (hG : G.Connected) (hab : a ≠ b) (F : ABTwoForestType G a b) :
    sumToAddedEdgeTree hG hab (Sum.inr F) =
      twoForest_to_addedEdgeTree hG hab F := rfl

@[simp] private theorem baseTree_to_addedEdgeTree_coe
    {V : Type*} {G : SimpleGraph V} {a b : V}
    (T : SimpleSpanningTreeType G) :
    (baseTree_to_addedEdgeTree (a := a) (b := b) T).1 = T.1 := rfl

@[simp] private theorem twoForest_to_addedEdgeTree_coe
    {V : Type*} [Fintype V] {G : SimpleGraph V} {a b : V}
    (hG : G.Connected) (hab : a ≠ b) (F : ABTwoForestType G a b) :
    (twoForest_to_addedEdgeTree hG hab F).1 =
      F.1 ⊔ SimpleGraph.edge a b := rfl

/-- Adding one previously absent edge partitions spanning trees into old
trees and separating two-forests.  This is the combinatorial all-minors
step; it contains no determinant statement. -/
noncomputable def addedEdgeTreeEquiv
    {V : Type*} [Fintype V] {G : SimpleGraph V} {a b : V}
    (hG : G.Connected) (hab : a ≠ b) (hnotadj : ¬G.Adj a b) :
    SimpleSpanningTreeType (G ⊔ SimpleGraph.edge a b) ≃
      SimpleSpanningTreeType G ⊕ ABTwoForestType G a b where
  toFun := addedEdgeTreeToSum hG hab hnotadj
  invFun := sumToAddedEdgeTree hG hab
  left_inv T := by
    classical
    by_cases hTab : T.1.Adj a b
    · rw [addedEdgeTreeToSum_of_adj hG hab hnotadj T hTab,
        sumToAddedEdgeTree_inr]
      apply Subtype.ext
      exact (addedEdgeTree_reconstruct T hTab).symm
    · rw [addedEdgeTreeToSum_of_not_adj hG hab hnotadj T hTab,
        sumToAddedEdgeTree_inl]
      apply Subtype.ext
      rfl
  right_inv S := by
    classical
    rcases S with T | F
    · have hnot : ¬T.1.Adj a b := fun h ↦ hnotadj (T.2.1 h)
      rw [sumToAddedEdgeTree_inl,
        addedEdgeTreeToSum_of_not_adj hG hab hnotadj _ hnot]
      apply congrArg Sum.inl
      apply Subtype.ext
      rfl
    · have hadj : (F.1 ⊔ SimpleGraph.edge a b).Adj a b := by
        right
        rw [SimpleGraph.edge_adj]
        exact ⟨Or.inl ⟨rfl, rfl⟩, hab⟩
      rw [sumToAddedEdgeTree_inr,
        addedEdgeTreeToSum_of_adj hG hab hnotadj _ hadj]
      apply congrArg Sum.inr
      apply Subtype.ext
      change ((F.1 ⊔ SimpleGraph.edge a b) ⊓ G) = F.1
      rw [inf_sup_right, inf_eq_left.mpr F.2.1,
        inf_comm (SimpleGraph.edge a b) G,
        inf_edge_eq_bot_of_not_adj' hnotadj, sup_bot_eq]

theorem treeCount_add_edge_eq_add_abTwoForestCount
    {V : Type*} [Fintype V] {G : SimpleGraph V} {a b : V}
    (hG : G.Connected) (hab : a ≠ b) (hnotadj : ¬G.Adj a b) :
    treeCount (G ⊔ SimpleGraph.edge a b) =
      treeCount G + abTwoForestCount G a b := by
  unfold treeCount abTwoForestCount
  rw [← Nat.card_sum]
  exact Nat.card_congr (addedEdgeTreeEquiv hG hab hnotadj)

private theorem lapMatrix_sup_of_adj_disjoint
    {V : Type*} [Fintype V] [DecidableEq V]
    (G H : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel H.Adj]
    [DecidableRel (G ⊔ H).Adj]
    (hdisjoint : ∀ u v, ¬(G.Adj u v ∧ H.Adj u v)) :
    (G ⊔ H).lapMatrix ℝ = G.lapMatrix ℝ + H.lapMatrix ℝ := by
  ext u v
  by_cases huv : u = v
  · subst v
    have hdegree : (((G ⊔ H).degree u : ℕ) : ℝ) =
        (G.degree u : ℝ) + H.degree u := by
      rw [(G ⊔ H).degree_eq_sum_if_adj (R := ℝ),
        G.degree_eq_sum_if_adj (R := ℝ),
        H.degree_eq_sum_if_adj (R := ℝ), ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro w _hw
      simp only [SimpleGraph.sup_adj]
      by_cases hGuw : G.Adj u w <;> by_cases hHuw : H.Adj u w
      · exact (hdisjoint u w ⟨hGuw, hHuw⟩).elim
      · simp [hGuw, hHuw]
      · simp [hGuw, hHuw]
      · simp [hGuw, hHuw]
    simpa [SimpleGraph.lapMatrix, SimpleGraph.degMatrix] using hdegree
  · simp only [SimpleGraph.lapMatrix, Matrix.sub_apply,
      SimpleGraph.degMatrix, SimpleGraph.adjMatrix_apply, Matrix.add_apply,
      SimpleGraph.sup_adj]
    simp only [Matrix.diagonal_apply_ne _ huv]
    by_cases hGuv : G.Adj u v <;> by_cases hHuv : H.Adj u v
    · exact (hdisjoint u v ⟨hGuv, hHuv⟩).elim
    · simp [hGuv, hHuv]
    · simp [hGuv, hHuv]
    · simp [hGuv, hHuv]

private theorem lapMatrix_sup_edge
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (a b : V) (hnotadj : ¬G.Adj a b) :
    (G ⊔ SimpleGraph.edge a b).lapMatrix ℝ =
      G.lapMatrix ℝ + (SimpleGraph.edge a b).lapMatrix ℝ := by
  classical
  apply lapMatrix_sup_of_adj_disjoint G (SimpleGraph.edge a b)
  intro u v huv
  rcases (SimpleGraph.edge_adj a b u v).mp huv.2 with
    ⟨⟨rfl, rfl⟩ | ⟨rfl, rfl⟩, _⟩
  · exact hnotadj huv.1
  · exact hnotadj huv.1.symm

private theorem edge_degree_left
    {V : Type*} [Fintype V] [DecidableEq V] (a b : V) (hab : a ≠ b) :
    (SimpleGraph.edge a b).degree a = 1 := by
  classical
  change ((SimpleGraph.edge a b).neighborFinset a).card = 1
  have hfin : (SimpleGraph.edge a b).neighborFinset a = {b} := by
    ext x
    rw [SimpleGraph.mem_neighborFinset]
    simp only [Finset.mem_singleton]
    rw [SimpleGraph.edge_adj]
    constructor
    · rintro ⟨(⟨_, hxb⟩ | ⟨hab', _⟩), _⟩
      · exact hxb
      · exact (hab hab').elim
    · intro hxb
      subst x
      exact ⟨Or.inl ⟨rfl, rfl⟩, hab⟩
  rw [hfin]
  simp

private theorem edge_degree_of_ne
    {V : Type*} [Fintype V] [DecidableEq V] (a b u : V)
    (hua : u ≠ a) (hub : u ≠ b) :
    (SimpleGraph.edge a b).degree u = 0 := by
  classical
  change ((SimpleGraph.edge a b).neighborFinset u).card = 0
  have hfin : (SimpleGraph.edge a b).neighborFinset u = ∅ := by
    ext x
    simp [SimpleGraph.mem_neighborFinset, SimpleGraph.edge_adj, hua, hub]
  rw [hfin]
  simp

private theorem reducedLapMatrix_sup_edge_eq_updateRow
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (a b : V) (hab : a ≠ b) (hnotadj : ¬G.Adj a b) :
    rayleighReducedLaplacian (G ⊔ SimpleGraph.edge a b) b =
      Matrix.updateRow (rayleighReducedLaplacian G b) ⟨a, hab⟩
        ((rayleighReducedLaplacian G b) ⟨a, hab⟩ +
          Pi.single ⟨a, hab⟩ 1) := by
  classical
  ext u v
  rw [Matrix.updateRow_apply]
  by_cases hua : u = ⟨a, hab⟩
  · subst u
    simp only [if_pos, Pi.add_apply]
    have hlap := congr_fun (congr_fun (lapMatrix_sup_edge G a b hnotadj) a) v.1
    change ((G ⊔ SimpleGraph.edge a b).lapMatrix ℝ) a v.1 =
      G.lapMatrix ℝ a v.1 +
        (Pi.single ⟨a, hab⟩ (1 : ℝ) : {v : V // v ≠ b} → ℝ) v
    rw [hlap, Matrix.add_apply]
    by_cases hva : v = ⟨a, hab⟩
    · subst v
      simp [SimpleGraph.lapMatrix, SimpleGraph.degMatrix,
        edge_degree_left a b hab]
    · have hvane : v.1 ≠ a := fun h ↦ hva (Subtype.ext h)
      have hvb : v.1 ≠ b := v.2
      simp [SimpleGraph.lapMatrix, SimpleGraph.degMatrix,
        SimpleGraph.edge_adj, hvane, hvane.symm, hvb, hva]
  · simp only [if_neg hua]
    have hlap := congr_fun (congr_fun
      (lapMatrix_sup_edge G a b hnotadj) u.1) v.1
    change ((G ⊔ SimpleGraph.edge a b).lapMatrix ℝ) u.1 v.1 =
      G.lapMatrix ℝ u.1 v.1
    rw [hlap, Matrix.add_apply]
    have huane : u.1 ≠ a := fun h ↦ hua (Subtype.ext h)
    have hub : u.1 ≠ b := u.2
    by_cases huv : u = v
    · subst v
      simp [SimpleGraph.lapMatrix, SimpleGraph.degMatrix,
        edge_degree_of_ne a b u.1 huane hub]
    · have huvval : u.1 ≠ v.1 := fun h ↦ huv (Subtype.ext h)
      have hvb : v.1 ≠ b := v.2
      simp [SimpleGraph.lapMatrix, SimpleGraph.degMatrix,
        SimpleGraph.edge_adj, huane, hub, hvb, huvval]

private theorem det_updateRow_add_single
    {n : Type*} [Fintype n] [DecidableEq n]
    (L : Matrix n n ℝ) (i : n) :
    (L.updateRow i (L i + Pi.single i 1)).det =
      L.det + L.adjugate i i := by
  rw [Matrix.det_updateRow_add, Matrix.updateRow_eq_self,
    ← Matrix.adjugate_apply]

/-- The diagonal all-minors identity for two distinct, previously
nonadjacent terminals follows from two ordinary Matrix--Tree cofactors: one
before and one after adjoining the terminal edge. -/
theorem abTwoForestCount_eq_adjugate_of_matrixTree
    (hMatrixTree : LabeledMultigraphCofactorInput.{u, u})
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.Connected) (a b : V) (hab : a ≠ b)
    (hnotadj : ¬G.Adj a b) :
    (abTwoForestCount G a b : ℝ) =
      (rayleighReducedLaplacian G b).adjugate ⟨a, hab⟩ ⟨a, hab⟩ := by
  classical
  let H := G ⊔ SimpleGraph.edge a b
  have hH : H.Connected := hG.mono le_sup_left
  have hcountNat : spanningForestCount H =
      spanningForestCount G + abTwoForestCount G a b := by
    rw [spanningForestCount_eq_treeCount hH,
      spanningForestCount_eq_treeCount hG]
    exact treeCount_add_edge_eq_add_abTwoForestCount hG hab hnotadj
  have hcountReal : (spanningForestCount H : ℝ) =
      spanningForestCount G + abTwoForestCount G a b := by
    exact_mod_cast hcountNat
  have hdetH :=
    spanningForestCount_eq_reducedLaplacian_det_of_matrixTree
      hMatrixTree H hH b
  have hdetG :=
    spanningForestCount_eq_reducedLaplacian_det_of_matrixTree
      hMatrixTree G hG b
  have hupdate : (rayleighReducedLaplacian H b).det =
      (rayleighReducedLaplacian G b).det +
        (rayleighReducedLaplacian G b).adjugate
          ⟨a, hab⟩ ⟨a, hab⟩ := by
    rw [reducedLapMatrix_sup_edge_eq_updateRow G a b hab hnotadj,
      det_updateRow_add_single]
  rw [hdetH, hdetG, hupdate] at hcountReal
  linarith

/-- The exact two cofactor identities used to identify the combinatorial
two-forest ratio with an inverse reduced-Laplacian entry.

This is an all-minors form of the Matrix--Tree interface used at this modular
layer.  It contains no inequality, monotonicity statement, half-plane
geometry, or asymptotic assertion, and is constructed downstream. -/
def TwoForestCofactorInput : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj]
    (a b : V) (hab : a ≠ b) (_hnotadj : ¬G.Adj a b)
      (_hG : G.Connected),
    let L := rayleighReducedLaplacian G b
    let ai : {v : V // v ≠ b} := ⟨a, hab⟩
    (spanningForestCount G : ℝ) = L.det ∧
      (abTwoForestCount G a b : ℝ) = L.adjugate ai ai

/-- The all-minors interface used below is a theorem, not a new trust
boundary: it is constructed from the existing labelled Matrix--Tree input. -/
theorem twoForestCofactorInput_of_matrixTree
    (hMatrixTree : LabeledMultigraphCofactorInput.{0, 0}) :
    TwoForestCofactorInput := by
  intro V _ _ G _ a b hab hnotadj hG
  exact ⟨spanningForestCount_eq_reducedLaplacian_det_of_matrixTree
      hMatrixTree G hG b,
    abTwoForestCount_eq_adjugate_of_matrixTree
      hMatrixTree G hG a b hab hnotadj⟩

/-! ## Positive definiteness of the reduced Laplacian -/

private theorem rayleighReducedLaplacian_posSemidef
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (root : V) :
    (rayleighReducedLaplacian G root).PosSemidef := by
  classical
  exact (G.posSemidef_lapMatrix ℝ).submatrix Subtype.val

theorem rayleighReducedLaplacian_posDef
    (hCofactor : TwoForestCofactorInput)
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.Connected) (a b : V) (hab : a ≠ b)
    (hnotadj : ¬G.Adj a b) :
    (rayleighReducedLaplacian G b).PosDef := by
  classical
  let L := rayleighReducedLaplacian G b
  have hdet : L.det ≠ 0 := by
    have hcount : 0 < spanningForestCount G := spanningForestCount_pos G
    have hcof : (spanningForestCount G : ℝ) = L.det :=
      (hCofactor G a b hab hnotadj hG).1
    rw [← hcof]
    exact ne_of_gt (by exact_mod_cast hcount)
  exact (rayleighReducedLaplacian_posSemidef G b).posDef_iff_det_ne_zero.mpr hdet

/-! ## The cofactor ratio is an inverse diagonal entry -/

theorem twoForestResistance_eq_inv_reducedLaplacian
    (hCofactor : TwoForestCofactorInput)
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.Connected) (a b : V) (hab : a ≠ b)
    (hnotadj : ¬G.Adj a b) :
    twoForestResistance G a b =
      (rayleighReducedLaplacian G b)⁻¹ ⟨a, hab⟩ ⟨a, hab⟩ := by
  classical
  let L := rayleighReducedLaplacian G b
  let ai : {v : V // v ≠ b} := ⟨a, hab⟩
  have hpos : 0 < (spanningForestCount G : ℝ) := by
    exact_mod_cast spanningForestCount_pos G
  have hdet : IsUnit L.det := by
    apply isUnit_iff_ne_zero.mpr
    intro hzero
    have hcof : (spanningForestCount G : ℝ) = L.det :=
      (hCofactor G a b hab hnotadj hG).1
    rw [← hcof] at hzero
    exact hpos.ne' hzero
  have htree : (spanningForestCount G : ℝ) = L.det :=
    (hCofactor G a b hab hnotadj hG).1
  have hforest : (abTwoForestCount G a b : ℝ) = L.adjugate ai ai :=
    (hCofactor G a b hab hnotadj hG).2
  change (abTwoForestCount G a b : ℝ) / spanningForestCount G = L⁻¹ ai ai
  rw [hforest, htree, Matrix.nonsing_inv_apply L hdet]
  change L.adjugate ai ai / L.det = ↑hdet.unit⁻¹ * L.adjugate ai ai
  rw [show ↑hdet.unit⁻¹ = (L.det)⁻¹ by simp]
  rw [div_eq_mul_inv, mul_comm]

/-! ## Laplacian energy increases when edges are added -/

private theorem laplacian_quadratic_mono
    {V : Type*} [Fintype V] [DecidableEq V]
    {G H : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel H.Adj]
    (hGH : G ≤ H)
    (x : V → ℝ) :
    Matrix.toLinearMap₂' ℝ (G.lapMatrix ℝ) x x ≤
      Matrix.toLinearMap₂' ℝ (H.lapMatrix ℝ) x x := by
  classical
  rw [SimpleGraph.lapMatrix_toLinearMap₂' ℝ G x,
    SimpleGraph.lapMatrix_toLinearMap₂' ℝ H x]
  apply (div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 2)).mpr
  apply Finset.sum_le_sum
  intro u _hu
  apply Finset.sum_le_sum
  intro v _hv
  by_cases hGuv : G.Adj u v
  · have hHuv : H.Adj u v := hGH hGuv
    simp [hGuv, hHuv]
  · by_cases hHuv : H.Adj u v
    · simp [hGuv, hHuv]
      positivity
    · simp [hGuv, hHuv]

private theorem lapMatrix_sub_posSemidef
    {V : Type*} [Fintype V] [DecidableEq V]
    {G H : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel H.Adj]
    (hGH : G ≤ H) :
    (H.lapMatrix ℝ - G.lapMatrix ℝ).PosSemidef := by
  classical
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · exact (H.isHermitian_lapMatrix ℝ).sub (G.isHermitian_lapMatrix ℝ)
  · intro x
    simp only [star_trivial, Matrix.sub_mulVec, dotProduct_sub]
    exact sub_nonneg.mpr (by
      simpa only [Matrix.toLinearMap₂'_apply'] using
        laplacian_quadratic_mono hGH x)

private theorem reducedLaplacian_sub_posSemidef
    {V : Type*} [Fintype V] [DecidableEq V]
    {G H : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel H.Adj]
    (hGH : G ≤ H)
    (root : V) :
    (rayleighReducedLaplacian H root -
      rayleighReducedLaplacian G root).PosSemidef := by
  classical
  have hsub := (lapMatrix_sub_posSemidef hGH).submatrix
    (fun v : {v : V // v ≠ root} ↦ v.1)
  convert hsub using 1
  ext u v
  rfl

/-! ## Dirichlet energy under graph embeddings -/

/-- Ordered adjacent pairs.  Each unoriented edge occurs twice; the factor
`1 / 2` in `dirichletEnergy` removes that duplication. -/
noncomputable def adjacencyPairFinset
    {V : Type*} [Fintype V] (G : SimpleGraph V) : Finset (V × V) := by
  classical
  exact Finset.univ.filter fun p ↦ G.Adj p.1 p.2

/-- Unit-conductance Dirichlet energy. -/
noncomputable def dirichletEnergy
    {V : Type*} [Fintype V] (G : SimpleGraph V) (f : V → ℝ) : ℝ := by
  classical
  exact (∑ p ∈ adjacencyPairFinset G, (f p.1 - f p.2) ^ 2) / 2

theorem dirichletEnergy_eq_pairSum
    {V : Type*} [Fintype V] (G : SimpleGraph V) (f : V → ℝ) :
    dirichletEnergy G f =
      (∑ p ∈ adjacencyPairFinset G, (f p.1 - f p.2) ^ 2) / 2 := by
  rfl

private theorem dirichletEnergy_eq_lapMatrix
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (f : V → ℝ) :
    dirichletEnergy G f = Matrix.toLinearMap₂' ℝ (G.lapMatrix ℝ) f f := by
  rw [dirichletEnergy_eq_pairSum,
    SimpleGraph.lapMatrix_toLinearMap₂' ℝ G f]
  simp only [adjacencyPairFinset, Finset.sum_filter]
  rw [Fintype.sum_prod_type]
  apply congrArg (fun t : ℝ ↦ t / 2)
  apply Fintype.sum_congr
  intro u
  apply Fintype.sum_congr
  intro v
  by_cases huv : G.Adj u v <;> simp [huv]

/-- An injective graph homomorphism.  Extra target vertices and edges are
allowed; this is the comparison direction needed for finite exhaustions. -/
structure InjectiveGraphHom
    {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W) where
  toEmbedding : V ↪ W
  map_adj : ∀ {u v}, G.Adj u v → H.Adj (toEmbedding u) (toEmbedding v)

namespace InjectiveGraphHom

variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

/-- Restrict a target potential along a graph embedding. -/
def pullback (e : InjectiveGraphHom G H) (f : W → ℝ) : V → ℝ :=
  fun v ↦ f (e.toEmbedding v)

/-- Adding vertices and edges increases Dirichlet energy after restriction
of a potential. -/
theorem dirichletEnergy_pullback_le
    [Fintype V] [Fintype W] (e : InjectiveGraphHom G H) (f : W → ℝ) :
    dirichletEnergy G (e.pullback f) ≤ dirichletEnergy H f := by
  classical
  let pe : V × V ↪ W × W := e.toEmbedding.prodMap e.toEmbedding
  have hsubset :
      (adjacencyPairFinset G).map pe ⊆ adjacencyPairFinset H := by
    intro p hp
    rw [Finset.mem_map] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    simp only [adjacencyPairFinset, Finset.mem_filter, Finset.mem_univ,
      true_and] at hq ⊢
    exact e.map_adj hq
  have hsum :
      ∑ p ∈ adjacencyPairFinset G,
          (e.pullback f p.1 - e.pullback f p.2) ^ 2 =
        ∑ p ∈ (adjacencyPairFinset G).map pe,
          (f p.1 - f p.2) ^ 2 := by
    rw [Finset.sum_map]
    rfl
  rw [dirichletEnergy_eq_pairSum, dirichletEnergy_eq_pairSum, hsum]
  apply (div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 2)).mpr
  exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
    (fun p _hp _hnot ↦ sq_nonneg (f p.1 - f p.2))

end InjectiveGraphHom

/-- The concave Dirichlet functional whose maximum is effective
resistance. -/
noncomputable def dirichletObjective
    {V : Type*} [Fintype V] (G : SimpleGraph V) (a b : V)
    (f : V → ℝ) : ℝ :=
  2 * (f a - f b) - dirichletEnergy G f

theorem InjectiveGraphHom.objective_le_pullback
    {V W : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W}
    (e : InjectiveGraphHom G H) (a b : V) (f : W → ℝ) :
    dirichletObjective H (e.toEmbedding a) (e.toEmbedding b) f ≤
      dirichletObjective G a b (e.pullback f) := by
  unfold dirichletObjective InjectiveGraphHom.pullback
  have henergy := e.dirichletEnergy_pullback_le f
  change dirichletEnergy G (fun v ↦ f (e.toEmbedding v)) ≤
    dirichletEnergy H f at henergy
  linarith

/-! ## The Dirichlet maximum on a connected graph -/

/-- Extend a vector indexed away from `root` by the value zero at `root`. -/
def rootZeroExtend
    {V : Type*} [Fintype V] [DecidableEq V] (root : V)
    (x : {v : V // v ≠ root} → ℝ) : V → ℝ :=
  fun v ↦ if h : v ≠ root then x ⟨v, h⟩ else 0

@[simp] theorem rootZeroExtend_root
    {V : Type*} [Fintype V] [DecidableEq V] (root : V)
    (x : {v : V // v ≠ root} → ℝ) :
    rootZeroExtend root x root = 0 := by
  simp [rootZeroExtend]

@[simp] theorem rootZeroExtend_subtype
    {V : Type*} [Fintype V] [DecidableEq V] (root : V)
    (x : {v : V // v ≠ root} → ℝ) (v : {v : V // v ≠ root}) :
    rootZeroExtend root x v.1 = x v := by
  simp [rootZeroExtend, v.2]

private theorem dirichletEnergy_rootZeroExtend
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (root : V)
    (x : {v : V // v ≠ root} → ℝ) :
    dirichletEnergy G (rootZeroExtend root x) =
      dotProduct x (rayleighReducedLaplacian G root *ᵥ x) := by
  rw [dirichletEnergy_eq_lapMatrix, Matrix.toLinearMap₂'_apply']
  simp only [dotProduct, Matrix.mulVec, rayleighReducedLaplacian,
    reducedLapMatrix, Matrix.submatrix_apply]
  rw [Fintype.sum_eq_add_sum_subtype_ne
    (fun u ↦ rootZeroExtend root x u *
      ∑ v, G.lapMatrix ℝ u v * rootZeroExtend root x v) root]
  simp only [rootZeroExtend_root, zero_mul, zero_add,
    rootZeroExtend_subtype]
  apply Fintype.sum_congr
  intro u
  congr 1
  rw [Fintype.sum_eq_add_sum_subtype_ne
    (fun v ↦ G.lapMatrix ℝ u.1 v * rootZeroExtend root x v) root]
  simp only [rootZeroExtend_root, mul_zero, zero_add,
    rootZeroExtend_subtype]

private theorem dirichletEnergy_sub_const
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    (f : V → ℝ) (c : ℝ) :
    dirichletEnergy G (fun v ↦ f v - c) = dirichletEnergy G f := by
  rw [dirichletEnergy_eq_pairSum, dirichletEnergy_eq_pairSum]
  apply congrArg (fun t : ℝ ↦ t / 2)
  apply Finset.sum_congr rfl
  intro p _hp
  congr 1
  ring

private theorem dirichletEnergy_eq_reduced
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (f : V → ℝ) (root : V) :
    dirichletEnergy G f =
      dotProduct (fun v : {v : V // v ≠ root} ↦ f v.1 - f root)
        (rayleighReducedLaplacian G root *ᵥ
          (fun v : {v : V // v ≠ root} ↦ f v.1 - f root)) := by
  let x : {v : V // v ≠ root} → ℝ := fun v ↦ f v.1 - f root
  calc
    dirichletEnergy G f = dirichletEnergy G (fun v ↦ f v - f root) :=
      (dirichletEnergy_sub_const G f (f root)).symm
    _ = dirichletEnergy G (rootZeroExtend root x) := by
      congr 1
      funext v
      by_cases hv : v = root
      · subst v
        simp [x]
      · simp [rootZeroExtend, hv, x]
    _ = dotProduct x (rayleighReducedLaplacian G root *ᵥ x) :=
      dirichletEnergy_rootZeroExtend G root x

/-- Completing the square for a positive-definite matrix. -/
private theorem quadratic_objective_le_inv_diagonal
    {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.PosDef) (i : n) (x : n → ℝ) :
    2 * x i - dotProduct x (A *ᵥ x) ≤ A⁻¹ i i := by
  let e : n → ℝ := Pi.single i 1
  have hAunit : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit
  have hAyInv : A *ᵥ (A⁻¹ *ᵥ e) = e := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A hAunit,
      Matrix.one_mulVec]
  have hnonneg := hA.posSemidef.dotProduct_mulVec_nonneg
    (x - A⁻¹ *ᵥ e)
  simp only [star_trivial, Matrix.mulVec_sub, dotProduct_sub,
    sub_dotProduct, hAyInv] at hnonneg
  have hAT : Aᵀ = A := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using hA.isHermitian.eq
  have hsymm :
      dotProduct (A⁻¹ *ᵥ e) (A *ᵥ x) = dotProduct e x := by
    calc
      dotProduct (A⁻¹ *ᵥ e) (A *ᵥ x) =
          dotProduct x (A *ᵥ (A⁻¹ *ᵥ e)) := by
            simpa only [hAT] using
              Matrix.dotProduct_transpose_mulVec A (A⁻¹ *ᵥ e) x
      _ = dotProduct x e := by rw [hAyInv]
      _ = dotProduct e x := dotProduct_comm x e
  have hei : dotProduct e x = x i := by simp [e]
  have heinv : dotProduct e (A⁻¹ *ᵥ e) = A⁻¹ i i := by simp [e]
  rw [hsymm, dotProduct_comm x e,
    dotProduct_comm (A⁻¹ *ᵥ e) e, hei, heinv] at hnonneg
  linarith

/-- On a connected graph, every potential's Dirichlet objective is bounded
above by the genuine two-forest ratio. -/
theorem dirichletObjective_le_twoForestResistance
    (hCofactor : TwoForestCofactorInput)
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.Connected) (a b : V) (hab : a ≠ b)
    (hnotadj : ¬G.Adj a b)
    (f : V → ℝ) :
    dirichletObjective G a b f ≤ twoForestResistance G a b := by
  let x : {v : V // v ≠ b} → ℝ := fun v ↦ f v.1 - f b
  rw [twoForestResistance_eq_inv_reducedLaplacian
    hCofactor G hG a b hab hnotadj]
  unfold dirichletObjective
  rw [dirichletEnergy_eq_reduced G f b]
  change 2 * x ⟨a, hab⟩ -
      dotProduct x (rayleighReducedLaplacian G b *ᵥ x) ≤ _
  exact quadratic_objective_le_inv_diagonal
    (rayleighReducedLaplacian_posDef hCofactor G hG a b hab hnotadj)
      ⟨a, hab⟩ x

/-- The canonical voltage potential obtained from the inverse reduced
Laplacian, normalized to vanish at `b`. -/
noncomputable def effectivePotential
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (a b : V) (hab : a ≠ b) : V → ℝ :=
  rootZeroExtend b
    ((rayleighReducedLaplacian G b)⁻¹ *ᵥ Pi.single ⟨a, hab⟩ 1)

/-- The canonical voltage attains the Dirichlet maximum. -/
theorem dirichletObjective_effectivePotential
    (hCofactor : TwoForestCofactorInput)
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.Connected) (a b : V) (hab : a ≠ b)
    (hnotadj : ¬G.Adj a b) :
    dirichletObjective G a b (effectivePotential G a b hab) =
      twoForestResistance G a b := by
  let L := rayleighReducedLaplacian G b
  let ai : {v : V // v ≠ b} := ⟨a, hab⟩
  let e : {v : V // v ≠ b} → ℝ := Pi.single ai 1
  let x : {v : V // v ≠ b} → ℝ := L⁻¹ *ᵥ e
  have hL : L.PosDef :=
    rayleighReducedLaplacian_posDef hCofactor G hG a b hab hnotadj
  have hunit : IsUnit L.det := (Matrix.isUnit_iff_isUnit_det L).mp hL.isUnit
  have hLx : L *ᵥ x = e := by
    dsimp only [x]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv L hunit,
      Matrix.one_mulVec]
  rw [twoForestResistance_eq_inv_reducedLaplacian
    hCofactor G hG a b hab hnotadj]
  unfold dirichletObjective effectivePotential
  rw [dirichletEnergy_rootZeroExtend]
  change 2 * (rootZeroExtend b x a - rootZeroExtend b x b) -
      dotProduct x (L *ᵥ x) = L⁻¹ ai ai
  have ha : rootZeroExtend b x a = x ai := by
    simpa only [ai] using rootZeroExtend_subtype b x ai
  rw [ha, rootZeroExtend_root]
  rw [hLx]
  have hxe : dotProduct x e = x ai := by simp [e, ai]
  have hdiag : x ai = L⁻¹ ai ai := by simp [x, e, ai]
  rw [hxe, hdiag]
  ring

/-- Rayleigh monotonicity across an injective graph embedding.  This form
allows a canonical exhaustion to have additional vertices as well as
additional edges. -/
theorem twoForestResistance_antitone_embedding
    (hCofactor : TwoForestCofactorInput)
    {V W : Type} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W}
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (e : InjectiveGraphHom G H) (hG : G.Connected) (hH : H.Connected)
    (a b : V) (hab : a ≠ b) (hGnotadj : ¬G.Adj a b)
    (hHnotadj : ¬H.Adj (e.toEmbedding a) (e.toEmbedding b)) :
    twoForestResistance H (e.toEmbedding a) (e.toEmbedding b) ≤
      twoForestResistance G a b := by
  have habH : e.toEmbedding a ≠ e.toEmbedding b :=
    fun h ↦ hab (e.toEmbedding.injective h)
  let f := effectivePotential H (e.toEmbedding a) (e.toEmbedding b) habH
  calc
    twoForestResistance H (e.toEmbedding a) (e.toEmbedding b) =
        dirichletObjective H (e.toEmbedding a) (e.toEmbedding b) f :=
      (dirichletObjective_effectivePotential hCofactor H hH
        (e.toEmbedding a) (e.toEmbedding b) habH hHnotadj).symm
    _ ≤ dirichletObjective G a b (e.pullback f) :=
      e.objective_le_pullback a b f
    _ ≤ twoForestResistance G a b :=
      dirichletObjective_le_twoForestResistance
        hCofactor G hG a b hab hGnotadj _

/-! ## Inverse quadratic forms are antitone in positive-definite order -/

private theorem inverse_diagonal_antitone
    {n : Type*} [Fintype n] [DecidableEq n]
    {A B : Matrix n n ℝ}
    (hA : A.PosDef) (hB : B.PosDef) (hBA : (B - A).PosSemidef)
    (i : n) : B⁻¹ i i ≤ A⁻¹ i i := by
  let e : n → ℝ := Pi.single i 1
  let y : n → ℝ := B⁻¹ *ᵥ e
  have hAunit : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit
  have hBunit : IsUnit B.det := (Matrix.isUnit_iff_isUnit_det B).mp hB.isUnit
  have hBy : B *ᵥ y = e := by
    dsimp only [y]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv B hBunit,
      Matrix.one_mulVec]
  have hAyInv : A *ᵥ (A⁻¹ *ᵥ e) = e :=
    by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A hAunit,
        Matrix.one_mulVec]
  have hdiff : 0 ≤ dotProduct y ((B - A) *ᵥ y) := by
    simpa only [star_trivial] using hBA.dotProduct_mulVec_nonneg y
  have hAcomplete :
      2 * dotProduct e y - dotProduct y (A *ᵥ y) ≤
        dotProduct e (A⁻¹ *ᵥ e) := by
    have hnonneg := hA.posSemidef.dotProduct_mulVec_nonneg
      (y - A⁻¹ *ᵥ e)
    simp only [star_trivial, Matrix.mulVec_sub, dotProduct_sub,
      sub_dotProduct, hAyInv] at hnonneg
    have hAT : Aᵀ = A := by
      simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using hA.isHermitian.eq
    have hsymm :
        dotProduct (A⁻¹ *ᵥ e) (A *ᵥ y) = dotProduct e y := by
      calc
        dotProduct (A⁻¹ *ᵥ e) (A *ᵥ y) =
            dotProduct y (A *ᵥ (A⁻¹ *ᵥ e)) := by
              simpa only [hAT] using
                Matrix.dotProduct_transpose_mulVec A (A⁻¹ *ᵥ e) y
        _ = dotProduct y e := by rw [hAyInv]
        _ = dotProduct e y := dotProduct_comm y e
    rw [hsymm, dotProduct_comm y e,
      dotProduct_comm (A⁻¹ *ᵥ e) e] at hnonneg
    linarith
  have hBenergy : dotProduct y (B *ᵥ y) = dotProduct e y := by
    rw [hBy, dotProduct_comm]
  have henergyOrder : dotProduct y (A *ᵥ y) ≤ dotProduct e y := by
    rw [← hBenergy]
    simpa only [Matrix.sub_mulVec, dotProduct_sub, sub_nonneg] using hdiff
  have hdiagB : dotProduct e (B⁻¹ *ᵥ e) = B⁻¹ i i := by
    simp [e]
  have hdiagA : dotProduct e (A⁻¹ *ᵥ e) = A⁻¹ i i := by
    simp [e]
  have hey : dotProduct e y = B⁻¹ i i := by
    simpa only [y] using hdiagB
  rw [← hey, ← hdiagA]
  linarith

/-! ## Finite Rayleigh monotonicity for the genuine two-forest ratio -/

/-- Adding edges to a connected finite graph cannot increase the
two-forest effective resistance.  The only external graph theorem used is
the explicit cofactor input above. -/
theorem twoForestResistance_antitone
    (hCofactor : TwoForestCofactorInput)
    {V : Type} [Fintype V] [DecidableEq V]
    {G H : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel H.Adj]
    (hG : G.Connected) (hGH : G ≤ H) (a b : V) (hab : a ≠ b)
    (hHnotadj : ¬H.Adj a b) :
    twoForestResistance H a b ≤ twoForestResistance G a b := by
  classical
  have hH : H.Connected := hG.mono hGH
  have hGnotadj : ¬G.Adj a b := fun h ↦ hHnotadj (hGH h)
  rw [twoForestResistance_eq_inv_reducedLaplacian
      hCofactor H hH a b hab hHnotadj,
    twoForestResistance_eq_inv_reducedLaplacian
      hCofactor G hG a b hab hGnotadj]
  exact inverse_diagonal_antitone
    (rayleighReducedLaplacian_posDef hCofactor G hG a b hab hGnotadj)
    (rayleighReducedLaplacian_posDef hCofactor H hH a b hab hHnotadj)
    (reducedLaplacian_sub_posSemidef hGH b) ⟨a, hab⟩

/-! ## One-sided finite half-plane exhaustion boundary -/

/-- The canonical finite words-on-a-page half-plane window.  It consists of
the points in the `X × Y` natural-coordinate box strictly preceding the
southeast corner `(z.1 + 1, z.2)`. -/
noncomputable def halfPlaneWindowVertices
    (z : Boundary.LatticePoint) (X Y : ℕ) :
    Finset Boundary.LatticePoint := by
  classical
  exact (Finset.range X ×ˢ Finset.range Y).filter fun w ↦
    wordsOnPageKey w < wordsOnPageKey (z.1 + 1, z.2)

@[simp] theorem mem_halfPlaneWindowVertices
    {z w : Boundary.LatticePoint} {X Y : ℕ} :
    w ∈ halfPlaneWindowVertices z X Y ↔
      w.1 < X ∧ w.2 < Y ∧
        wordsOnPageKey w < wordsOnPageKey (z.1 + 1, z.2) := by
  classical
  simp [halfPlaneWindowVertices, and_assoc]

/-- The induced square-lattice graph on a canonical finite half-plane
window. -/
noncomputable abbrev halfPlaneWindowGraph
    (z : Boundary.LatticePoint) (X Y : ℕ) :=
  Boundary.faceGraph (halfPlaneWindowVertices z X Y)

private theorem wordsOnPageKey_sw_lt_se (z : Boundary.LatticePoint) :
    wordsOnPageKey z < wordsOnPageKey (z.1 + 1, z.2) := by
  rw [wordsOnPageKey, wordsOnPageKey, Prod.Lex.toLex_lt_toLex]
  exact Or.inr ⟨rfl, by omega⟩

private theorem wordsOnPageKey_ne_lt_se (z : Boundary.LatticePoint) :
    wordsOnPageKey (z.1 + 1, z.2 + 1) <
      wordsOnPageKey (z.1 + 1, z.2) := by
  rw [wordsOnPageKey, wordsOnPageKey, Prod.Lex.toLex_lt_toLex]
  left
  omega

/-- Southwest terminal in the canonical window. -/
def halfPlaneWindowSW
    (z : Boundary.LatticePoint) (X Y : ℕ)
    (hx : z.1 < X) (hy : z.2 < Y) :
    {w // w ∈ halfPlaneWindowVertices z X Y} :=
  ⟨z, mem_halfPlaneWindowVertices.mpr
    ⟨hx, hy, wordsOnPageKey_sw_lt_se z⟩⟩

/-- Northeast terminal in the canonical window. -/
def halfPlaneWindowNE
    (z : Boundary.LatticePoint) (X Y : ℕ)
    (hx : z.1 + 1 < X) (hy : z.2 + 1 < Y) :
    {w // w ∈ halfPlaneWindowVertices z X Y} :=
  ⟨(z.1 + 1, z.2 + 1), mem_halfPlaneWindowVertices.mpr
    ⟨hx, hy, wordsOnPageKey_ne_lt_se z⟩⟩

private theorem faceGraph_reachable_horizontal_le
    (S : Finset Boundary.LatticePoint) (y x x' : ℕ) (hxx' : x ≤ x')
    (hmem : ∀ t, x ≤ t → t ≤ x' → (t, y) ∈ S) :
    (Boundary.faceGraph S).Reachable
      ⟨(x, y), hmem x le_rfl hxx'⟩
      ⟨(x', y), hmem x' hxx' le_rfl⟩ := by
  induction x', hxx' using Nat.le_induction with
  | base => exact SimpleGraph.Reachable.refl _
  | succ n hxn ih =>
      have hmem' : ∀ t, x ≤ t → t ≤ n → (t, y) ∈ S :=
        fun t hxt htn ↦ hmem t hxt (htn.trans (Nat.le_succ n))
      have hr := ih hmem'
      have hnmem : (n, y) ∈ S := hmem n hxn (Nat.le_succ n)
      have hsnmem : (n + 1, y) ∈ S :=
        hmem (n + 1) (hxn.trans (Nat.le_succ n)) le_rfl
      have hadj : (Boundary.faceGraph S).Adj
          ⟨(n, y), hnmem⟩ ⟨(n + 1, y), hsnmem⟩ := by
        apply (Boundary.faceLattice_adj_iff_step _ _).mpr
        simp [Boundary.latticePointToPoint,
          SquareMaximality.ClosedWalk.Step.vector_east,
          SquareMaximality.ClosedWalk.Step.vector_west,
          SquareMaximality.ClosedWalk.Step.vector_north,
          SquareMaximality.ClosedWalk.Step.vector_south]
      exact hr.trans hadj.reachable

private theorem faceGraph_reachable_horizontal
    (S : Finset Boundary.LatticePoint) (y x x' : ℕ)
    (hmem : ∀ t, min x x' ≤ t → t ≤ max x x' → (t, y) ∈ S) :
    (Boundary.faceGraph S).Reachable
      ⟨(x, y), hmem x (min_le_left _ _) (le_max_left _ _)⟩
      ⟨(x', y), hmem x' (min_le_right _ _) (le_max_right _ _)⟩ := by
  rcases le_total x x' with hxx' | hx'x
  · have hm : ∀ t, x ≤ t → t ≤ x' → (t, y) ∈ S := by
      intro t hxt htx'
      apply hmem t
      · simpa [min_eq_left hxx'] using hxt
      · simpa [max_eq_right hxx'] using htx'
    have hr := faceGraph_reachable_horizontal_le S y x x' hxx' hm
    exact hr
  · have hm : ∀ t, x' ≤ t → t ≤ x → (t, y) ∈ S := by
      intro t hx't htx
      apply hmem t
      · simpa [min_eq_right hx'x] using hx't
      · simpa [max_eq_left hx'x] using htx
    have hr := (faceGraph_reachable_horizontal_le S y x' x hx'x hm).symm
    exact hr

private theorem faceGraph_reachable_vertical_le
    (S : Finset Boundary.LatticePoint) (x y y' : ℕ) (hyy' : y ≤ y')
    (hmem : ∀ t, y ≤ t → t ≤ y' → (x, t) ∈ S) :
    (Boundary.faceGraph S).Reachable
      ⟨(x, y), hmem y le_rfl hyy'⟩
      ⟨(x, y'), hmem y' hyy' le_rfl⟩ := by
  induction y', hyy' using Nat.le_induction with
  | base => exact SimpleGraph.Reachable.refl _
  | succ n hyn ih =>
      have hmem' : ∀ t, y ≤ t → t ≤ n → (x, t) ∈ S :=
        fun t hyt htn ↦ hmem t hyt (htn.trans (Nat.le_succ n))
      have hr := ih hmem'
      have hnmem : (x, n) ∈ S := hmem n hyn (Nat.le_succ n)
      have hsnmem : (x, n + 1) ∈ S :=
        hmem (n + 1) (hyn.trans (Nat.le_succ n)) le_rfl
      have hadj : (Boundary.faceGraph S).Adj
          ⟨(x, n), hnmem⟩ ⟨(x, n + 1), hsnmem⟩ := by
        apply (Boundary.faceLattice_adj_iff_step _ _).mpr
        simp [Boundary.latticePointToPoint,
          SquareMaximality.ClosedWalk.Step.vector_east,
          SquareMaximality.ClosedWalk.Step.vector_west,
          SquareMaximality.ClosedWalk.Step.vector_north,
          SquareMaximality.ClosedWalk.Step.vector_south]
      exact hr.trans hadj.reachable

private theorem wordsOnPageKey_lt_se_iff
    (z w : Boundary.LatticePoint) :
    wordsOnPageKey w < wordsOnPageKey (z.1 + 1, z.2) ↔
      z.2 < w.2 ∨ (w.2 = z.2 ∧ w.1 ≤ z.1) := by
  rw [wordsOnPageKey, wordsOnPageKey, Prod.Lex.toLex_lt_toLex]
  constructor
  · rintro (hrow | ⟨hrow, hxrow⟩)
    · left
      omega
    · right
      constructor <;> omega
  · rintro (hrow | ⟨hrow, hxrow⟩)
    · left
      omega
    · right
      constructor <;> omega

/-- Every sufficiently large canonical half-plane window is connected.  Its
shape is the full strip above row `z.2`, together with the bottom segment
ending at `z`. -/
theorem halfPlaneWindowGraph_connected
    (z : Boundary.LatticePoint) (X Y : ℕ)
    (hx : z.1 + 1 < X) (hy : z.2 + 1 < Y) :
    (halfPlaneWindowGraph z X Y).Connected := by
  let sw := halfPlaneWindowSW z X Y (by omega) (by omega)
  letI : Nonempty {w // w ∈ halfPlaneWindowVertices z X Y} := ⟨sw⟩
  apply SimpleGraph.Connected.mk
  intro u v
  have reach_sw (q : {w // w ∈ halfPlaneWindowVertices z X Y}) :
      (halfPlaneWindowGraph z X Y).Reachable q sw := by
    let qx := q.1.1
    let qy := q.1.2
    have hqmem := mem_halfPlaneWindowVertices.mp q.2
    have hqxX : qx < X := hqmem.1
    have hqyY : qy < Y := hqmem.2.1
    have hshape : z.2 < qy ∨ (qy = z.2 ∧ qx ≤ z.1) :=
      (wordsOnPageKey_lt_se_iff z q.1).mp hqmem.2.2
    rcases hshape with hqy | ⟨hqy, hqx⟩
    · have hy1 : z.2 + 1 ≤ qy := by omega
      have hv := (faceGraph_reachable_vertical_le
        (halfPlaneWindowVertices z X Y) qx (z.2 + 1) qy hy1 (by
          intro t hlow thigh
          apply mem_halfPlaneWindowVertices.mpr
          refine ⟨hqxX, by omega, ?_⟩
          apply (wordsOnPageKey_lt_se_iff z (qx, t)).mpr
          left
          omega)).symm
      have hh := faceGraph_reachable_horizontal
        (halfPlaneWindowVertices z X Y) (z.2 + 1) qx z.1 (by
          intro t hmin hmax
          apply mem_halfPlaneWindowVertices.mpr
          refine ⟨by omega, by omega, ?_⟩
          apply (wordsOnPageKey_lt_se_iff z (t, z.2 + 1)).mpr
          left
          omega)
      have hs : (halfPlaneWindowGraph z X Y).Adj
          ⟨(z.1, z.2 + 1), by
            apply mem_halfPlaneWindowVertices.mpr
            refine ⟨by omega, by omega, ?_⟩
            apply (wordsOnPageKey_lt_se_iff z (z.1, z.2 + 1)).mpr
            left
            omega⟩ sw := by
        change Boundary.faceLattice.Adj (z.1, z.2 + 1) z
        apply (Boundary.faceLattice_adj_iff_step _ _).mpr
        simp [Boundary.latticePointToPoint,
          SquareMaximality.ClosedWalk.Step.vector_east,
          SquareMaximality.ClosedWalk.Step.vector_west,
          SquareMaximality.ClosedWalk.Step.vector_north,
          SquareMaximality.ClosedWalk.Step.vector_south]
      exact hv.trans (hh.trans hs.reachable)
    · have hr := faceGraph_reachable_horizontal
        (halfPlaneWindowVertices z X Y) z.2 qx z.1 (by
          intro t hmin hmax
          apply mem_halfPlaneWindowVertices.mpr
          refine ⟨by omega, by omega, ?_⟩
          apply (wordsOnPageKey_lt_se_iff z (t, z.2)).mpr
          right
          exact ⟨rfl, by omega⟩)
      have hq : q.1 = (qx, z.2) := by
        apply Prod.ext
        · rfl
        · exact hqy
      have hsw : sw.1 = z := by rfl
      convert hr using 1
      · exact Subtype.ext hq
      · exact Subtype.ext hsw
  exact (reach_sw u).trans (reach_sw v).symm

/-- The concrete one-sided finite statement left by Tapp's entropy
contradiction.  It quantifies only the canonical box-truncated half-plane
family; no arbitrary prefix graph and no target resistance inequality occurs
in its definition. -/
def CanonicalHalfPlaneMultiplierLowerBound (κ : ℝ) : Prop :=
  ∀ (z : Boundary.LatticePoint) (X Y : ℕ)
    (hx : z.1 + 1 < X) (hy : z.2 + 1 < Y),
    Real.exp κ ≤
      2 + twoForestResistance (halfPlaneWindowGraph z X Y)
        (halfPlaneWindowSW z X Y (by omega) (by omega))
        (halfPlaneWindowNE z X Y hx hy)

/-! ### Every finite prefix embeds in a sufficiently large window -/

/-- The exposed vertices, with future isolated vertices removed from the
ambient type. -/
abbrev PrefixVertex
    {V : Type*} [Fintype V] (coord : V ↪ Boundary.LatticePoint) (k : ℕ) :=
  {v : V // v ∈ wordsPrefixVertices coord k}

/-- The graph induced by a words-on-a-page prefix on its actually exposed
vertices. -/
noncomputable def prefixVertexGraph
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    (coord : V ↪ Boundary.LatticePoint) (k : ℕ) :
    SimpleGraph (PrefixVertex coord k) := by
  classical
  exact (wordsPrefixGraph G coord k).comap Subtype.val

private theorem wordsOnPageKey_lt_current_of_mem_prefix
    {V : Type*} [Fintype V] (coord : V ↪ Boundary.LatticePoint)
    (k : ℕ) (hk : k < Fintype.card V) (v : V)
    (hv : v ∈ wordsPrefixVertices coord k) :
    wordsOnPageKey (coord v) <
      wordsOnPageKey
        (coord ((wordsOnPageOrderIso coord).toEquiv ⟨k, hk⟩)) := by
  have hvIndex :
      (wordsOnPageOrderIso coord).toEquiv.symm v < ⟨k, hk⟩ := by
    change ((wordsOnPageOrderIso coord).toEquiv.symm v).1 < k
    simpa only [wordsPrefixVertices, Finset.mem_filter, Finset.mem_univ,
      true_and] using hv
  letI : LinearOrder V := wordsOnPageLinearOrder coord
  have hvOrder :
      v < (wordsOnPageOrderIso coord).toEquiv ⟨k, hk⟩ := by
    simpa using (wordsOnPageOrderIso coord).lt_iff_lt.mpr hvIndex
  exact hvOrder

/-- Coordinate embedding of an exposed prefix into any canonical window
whose box contains all ambient coordinates. -/
noncomputable def prefixToHalfPlaneWindow
    {V : Type} [Fintype V]
    (coord : V ↪ Boundary.LatticePoint)
    (k : ℕ) (hk : k < Fintype.card V) (z : Boundary.LatticePoint)
    (hcoord : coord ((wordsOnPageOrderIso coord).toEquiv ⟨k, hk⟩) =
      (z.1 + 1, z.2))
    (X Y : ℕ) (hX : ∀ v, (coord v).1 < X)
    (hY : ∀ v, (coord v).2 < Y) :
    PrefixVertex coord k ↪
      {w // w ∈ halfPlaneWindowVertices z X Y} where
  toFun v := ⟨coord v.1, mem_halfPlaneWindowVertices.mpr ⟨hX v.1, hY v.1, by
    have hkey := wordsOnPageKey_lt_current_of_mem_prefix
      coord k hk v.1 v.2
    rw [hcoord] at hkey
    exact hkey⟩⟩
  inj' u v huv := by
    apply Subtype.ext
    exact coord.injective (congrArg Subtype.val huv)

/-- The prefix coordinate embedding is a graph homomorphism into the
canonical induced lattice graph.  Thus the window is the supergraph in the
correct Rayleigh direction. -/
noncomputable def prefixGraphHomToHalfPlaneWindow
    {V : Type} [Fintype V] (G : SimpleGraph V)
    (coord : V ↪ Boundary.LatticePoint)
    (k : ℕ) (hk : k < Fintype.card V) (z : Boundary.LatticePoint)
    (hLattice : G ≤ Boundary.faceLattice.comap coord)
    (hcoord : coord ((wordsOnPageOrderIso coord).toEquiv ⟨k, hk⟩) =
      (z.1 + 1, z.2))
    (X Y : ℕ) (hX : ∀ v, (coord v).1 < X)
    (hY : ∀ v, (coord v).2 < Y) :
    InjectiveGraphHom (prefixVertexGraph G coord k)
      (halfPlaneWindowGraph z X Y) where
  toEmbedding := prefixToHalfPlaneWindow coord k hk z hcoord X Y hX hY
  map_adj := by
    intro u v huv
    exact hLattice huv.1

/-- Every finite coordinate embedding admits box bounds large enough for
the canonical exhaustion comparison. -/
theorem exists_halfPlaneWindow_coordinate_bounds
    {V : Type} [Fintype V] (coord : V ↪ Boundary.LatticePoint)
    (z : Boundary.LatticePoint) :
    ∃ X Y,
      z.1 + 1 < X ∧ z.2 + 1 < Y ∧
      (∀ v, (coord v).1 < X) ∧ ∀ v, (coord v).2 < Y := by
  classical
  obtain ⟨X₀, hX₀⟩ := Finset.exists_nat_subset_range
    (Finset.univ.image fun v : V ↦ (coord v).1)
  obtain ⟨Y₀, hY₀⟩ := Finset.exists_nat_subset_range
    (Finset.univ.image fun v : V ↦ (coord v).2)
  refine ⟨max X₀ (z.1 + 2), max Y₀ (z.2 + 2), by omega, by omega, ?_, ?_⟩
  · intro v
    have hv : (coord v).1 ∈ Finset.range X₀ := hX₀ (Finset.mem_image.mpr
      ⟨v, Finset.mem_univ v, rfl⟩)
    simp only [Finset.mem_range] at hv
    omega
  · intro v
    have hv : (coord v).2 ∈ Finset.range Y₀ := hY₀ (Finset.mem_image.mpr
      ⟨v, Finset.mem_univ v, rfl⟩)
    simp only [Finset.mem_range] at hv
    omega

/-! ### Connected terminal components -/

/-- Vertices in the connected component of `a`. -/
abbrev ReachableVertex
    {V : Type*} (G : SimpleGraph V) (a : V) :=
  {v : V // G.Reachable a v}

/-- The graph induced on the connected component of `a`. -/
def reachableComponentGraph
    {V : Type*} (G : SimpleGraph V) (a : V) :
    SimpleGraph (ReachableVertex G a) :=
  G.comap Subtype.val

private theorem reachableComponentGraph_reachable_iff
    {V : Type*} {G : SimpleGraph V} {a : V}
    (u v : ReachableVertex G a) :
    (reachableComponentGraph G a).Reachable u v ↔
      G.Reachable u.1 v.1 := by
  constructor
  · intro huv
    exact huv.map
      { toFun := Subtype.val
        map_rel' := fun h ↦ h }
  · intro huv
    rw [SimpleGraph.reachable_iff_reflTransGen] at huv ⊢
    have liftFrom (w : V)
        (huw : Relation.ReflTransGen G.Adj u.1 w) :
        ∃ w' : ReachableVertex G a, w'.1 = w ∧
          Relation.ReflTransGen (reachableComponentGraph G a).Adj u w' := by
      induction huw with
      | refl => exact ⟨u, rfl, Relation.ReflTransGen.refl⟩
      | @tail y z _ hyz ih =>
          obtain ⟨y', rfl, huy'⟩ := ih
          let z' : ReachableVertex G a :=
            ⟨z, y'.2.trans hyz.reachable⟩
          refine ⟨z', rfl, huy'.tail ?_⟩
          exact hyz
    obtain ⟨v', hv', huv'⟩ := liftFrom v.1 huv
    have hvEq : v' = v := Subtype.ext hv'
    exact hvEq ▸ huv'

/-- The induced graph on a reachable component is connected. -/
theorem reachableComponentGraph_connected
    {V : Type*} (G : SimpleGraph V) (a : V) :
    (reachableComponentGraph G a).Connected := by
  let a' : ReachableVertex G a := ⟨a, SimpleGraph.Reachable.refl a⟩
  letI : Nonempty (ReachableVertex G a) := ⟨a'⟩
  apply SimpleGraph.Connected.mk
  intro u v
  apply (reachableComponentGraph_reachable_iff u v).mpr
  exact u.2.symm.trans v.2

/-- Restrict a graph embedding to the connected component of a terminal. -/
def InjectiveGraphHom.restrictReachableComponent
    {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (e : InjectiveGraphHom G H) (a : V) :
    InjectiveGraphHom (reachableComponentGraph G a) H where
  toEmbedding :=
    { toFun := fun v ↦ e.toEmbedding v.1
      inj' := fun _ _ huv ↦ Subtype.ext (e.toEmbedding.injective huv) }
  map_adj := fun huv ↦ e.map_adj huv

/-! ### Cancellation of components disjoint from the terminals -/

private theorem reachable_sum_inl_iff
    {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (u v : V) :
    (G ⊕g H).Reachable (Sum.inl u) (Sum.inl v) ↔ G.Reachable u v := by
  rw [SimpleGraph.reachable_iff_reflTransGen,
    SimpleGraph.reachable_iff_reflTransGen]
  constructor
  · intro h
    have project : ∀ {z : V ⊕ W},
        Relation.ReflTransGen (G ⊕g H).Adj (Sum.inl u) z →
          match z with
          | Sum.inl w => Relation.ReflTransGen G.Adj u w
          | Sum.inr _ => False := by
      intro z huz
      induction huz with
      | refl => exact Relation.ReflTransGen.refl
      | @tail y z _ hyz ih =>
          cases y with
          | inl y =>
              cases z with
              | inl z => exact ih.tail hyz
              | inr z => simp at hyz
          | inr y => exact ih.elim
    exact project h
  · intro h
    exact Relation.ReflTransGen.lift
      (p := (G ⊕g H).Adj) (Sum.inl : V → V ⊕ W)
      (fun _ _ hadj ↦ hadj) _ _ h

private theorem reachable_sum_inr_iff
    {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (u v : W) :
    (G ⊕g H).Reachable (Sum.inr u) (Sum.inr v) ↔ H.Reachable u v := by
  rw [SimpleGraph.reachable_iff_reflTransGen,
    SimpleGraph.reachable_iff_reflTransGen]
  constructor
  · intro h
    have project : ∀ {z : V ⊕ W},
        Relation.ReflTransGen (G ⊕g H).Adj (Sum.inr u) z →
          match z with
          | Sum.inl _ => False
          | Sum.inr w => Relation.ReflTransGen H.Adj u w := by
      intro z huz
      induction huz with
      | refl => exact Relation.ReflTransGen.refl
      | @tail y z _ hyz ih =>
          cases y with
          | inl y => exact ih.elim
          | inr y =>
              cases z with
              | inl z => simp at hyz
              | inr z => exact ih.tail hyz
    exact project h
  · intro h
    exact Relation.ReflTransGen.lift
      (p := (G ⊕g H).Adj) (Sum.inr : W → V ⊕ W)
      (fun _ _ hadj ↦ hadj) _ _ h

private theorem deleteEdges_sum_inl
    {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W) (u v : V) :
    (G ⊕g H).deleteEdges {s(Sum.inl u, Sum.inl v)} =
      (G.deleteEdges {s(u, v)}) ⊕g H := by
  ext x y
  rcases x with x | x <;> rcases y with y | y <;>
    simp [SimpleGraph.deleteEdges]

private theorem deleteEdges_sum_inr
    {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W) (u v : W) :
    (G ⊕g H).deleteEdges {s(Sum.inr u, Sum.inr v)} =
      G ⊕g (H.deleteEdges {s(u, v)}) := by
  ext x y
  rcases x with x | x <;> rcases y with y | y <;>
    simp [SimpleGraph.deleteEdges]

private theorem isAcyclic_sum
    {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (hG : G.IsAcyclic) (hH : H.IsAcyclic) :
    (G ⊕g H).IsAcyclic := by
  rw [SimpleGraph.isAcyclic_iff_forall_isBridge]
  rintro ⟨x, y⟩ hxy
  rw [SimpleGraph.mem_edgeSet] at hxy
  rcases x with x | x <;> rcases y with y | y
  · have hb := (SimpleGraph.isAcyclic_iff_forall_isBridge.mp hG)
        ((SimpleGraph.mem_edgeSet G).mpr hxy)
    rw [SimpleGraph.isBridge_iff] at hb ⊢
    rw [deleteEdges_sum_inl]
    exact fun hr ↦ hb ((reachable_sum_inl_iff x y).mp hr)
  · simp at hxy
  · simp at hxy
  · have hb := (SimpleGraph.isAcyclic_iff_forall_isBridge.mp hH)
        ((SimpleGraph.mem_edgeSet H).mpr hxy)
    rw [SimpleGraph.isBridge_iff] at hb ⊢
    rw [deleteEdges_sum_inr]
    exact fun hr ↦ hb ((reachable_sum_inr_iff x y).mp hr)

private theorem sum_comap_eq_of_le
    {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    {K : SimpleGraph (V ⊕ W)} (hK : K ≤ G ⊕g H) :
    (K.comap (Sum.inl : V → V ⊕ W)) ⊕g
        (K.comap (Sum.inr : W → V ⊕ W)) = K := by
  ext x y
  rcases x with x | x <;> rcases y with y | y
  · rfl
  · constructor
    · intro h
      simp at h
    · intro h
      have := hK h
      simp at this
  · constructor
    · intro h
      simp at h
    · intro h
      have := hK h
      simp at this
  · rfl

private theorem reachable_comap_inl_iff_of_le_sum
    {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    {K : SimpleGraph (V ⊕ W)} (hK : K ≤ G ⊕g H) (u v : V) :
    (K.comap (Sum.inl : V → V ⊕ W)).Reachable u v ↔
      K.Reachable (Sum.inl u) (Sum.inl v) := by
  rw [← sum_comap_eq_of_le hK]
  exact (reachable_sum_inl_iff u v).symm

private theorem reachable_comap_inr_iff_of_le_sum
    {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    {K : SimpleGraph (V ⊕ W)} (hK : K ≤ G ⊕g H) (u v : W) :
    (K.comap (Sum.inr : W → V ⊕ W)).Reachable u v ↔
      K.Reachable (Sum.inr u) (Sum.inr v) := by
  rw [← sum_comap_eq_of_le hK]
  exact (reachable_sum_inr_iff u v).symm

/-- A maximal forest of a disjoint graph sum is exactly a pair of maximal
forests of the summands. -/
noncomputable def spanningForestSumEquiv
    {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W) :
    SpanningForestType (G ⊕g H) ≃
      SpanningForestType G × SpanningForestType H where
  toFun F := by
    let FG : SimpleGraph V := F.1.comap (Sum.inl : V → V ⊕ W)
    let FH : SimpleGraph W := F.1.comap (Sum.inr : W → V ⊕ W)
    refine (⟨FG, ?_, ?_, ?_⟩, ⟨FH, ?_, ?_, ?_⟩)
    · intro u v huv
      exact F.2.1 huv
    · exact F.2.2.1.of_comap
        ⟨Sum.inl, Sum.inl_injective⟩
    · ext u v
      rw [reachable_comap_inl_iff_of_le_sum F.2.1, F.2.2.2]
      exact reachable_sum_inl_iff u v
    · intro u v huv
      exact F.2.1 huv
    · exact F.2.2.1.of_comap
        ⟨Sum.inr, Sum.inr_injective⟩
    · ext u v
      rw [reachable_comap_inr_iff_of_le_sum F.2.1, F.2.2.2]
      exact reachable_sum_inr_iff u v
  invFun F := by
    refine ⟨F.1.1 ⊕g F.2.1, ?_, ?_, ?_⟩
    · intro x y hxy
      rcases x with x | x <;> rcases y with y | y
      · exact F.1.2.1 hxy
      · simp at hxy
      · simp at hxy
      · exact F.2.2.1 hxy
    · exact isAcyclic_sum F.1.2.2.1 F.2.2.2.1
    · ext x y
      rcases x with x | x <;> rcases y with y | y
      · rw [reachable_sum_inl_iff, reachable_sum_inl_iff, F.1.2.2.2]
      · constructor
        · exact fun h ↦ (SimpleGraph.not_reachable_sum_inl_inr x y h).elim
        · exact fun h ↦ (SimpleGraph.not_reachable_sum_inl_inr x y h).elim
      · constructor
        · exact fun h ↦
            (SimpleGraph.not_reachable_sum_inl_inr y x h.symm).elim
        · exact fun h ↦
            (SimpleGraph.not_reachable_sum_inl_inr y x h.symm).elim
      · rw [reachable_sum_inr_iff, reachable_sum_inr_iff, F.2.2.2.2]
  left_inv F := by
    apply Subtype.ext
    exact sum_comap_eq_of_le F.2.1
  right_inv F := by
    apply Prod.ext
    · apply Subtype.ext
      rfl
    · apply Subtype.ext
      rfl

/-- Maximal-forest counts multiply over disjoint graph sums. -/
theorem spanningForestCount_sum
    {V W : Type*} [Finite V] [Finite W]
    (G : SimpleGraph V) (H : SimpleGraph W) :
    spanningForestCount (G ⊕g H) =
      spanningForestCount G * spanningForestCount H := by
  rw [spanningForestCount, spanningForestCount, spanningForestCount,
    Nat.card_congr (spanningForestSumEquiv G H), Nat.card_prod]

private theorem sup_edge_inl_sum_comap_eq
    {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    {K : SimpleGraph (V ⊕ W)} (hK : K ≤ G ⊕g H) (a b : V) :
    ((K.comap (Sum.inl : V → V ⊕ W)) ⊔ SimpleGraph.edge a b) ⊕g
        (K.comap (Sum.inr : W → V ⊕ W)) =
      K ⊔ SimpleGraph.edge (Sum.inl a) (Sum.inl b) := by
  ext x y
  rcases x with x | x <;> rcases y with y | y
  · simp [SimpleGraph.edge]
  · have hn : ¬K.Adj (Sum.inl x) (Sum.inr y) := by
      intro h
      have := hK h
      simp at this
    simp [SimpleGraph.edge, hn]
  · have hn : ¬K.Adj (Sum.inr x) (Sum.inl y) := by
      intro h
      have := hK h
      simp at this
    simp [SimpleGraph.edge, hn]
  · simp [SimpleGraph.edge]

/-- A separating two-forest in the left summand of a disjoint graph sum is
exactly a left separating two-forest together with a maximal forest in the
right summand. -/
noncomputable def abTwoForestSumEquiv
    {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W) (a b : V) :
    ABTwoForestType (G ⊕g H) (Sum.inl a) (Sum.inl b) ≃
      ABTwoForestType G a b × SpanningForestType H where
  toFun F := by
    let FG : SimpleGraph V := F.1.comap (Sum.inl : V → V ⊕ W)
    let FH : SimpleGraph W := F.1.comap (Sum.inr : W → V ⊕ W)
    have hsup := sup_edge_inl_sum_comap_eq F.2.1 a b
    refine (⟨FG, ?_, ?_, ?_, ?_⟩, ⟨FH, ?_, ?_, ?_⟩)
    · intro u v huv
      exact F.2.1 huv
    · exact F.2.2.1.of_comap ⟨Sum.inl, Sum.inl_injective⟩
    · intro hab
      exact F.2.2.2.1 ((reachable_comap_inl_iff_of_le_sum F.2.1 a b).mp hab)
    · ext u v
      have hdecomp :
          ((FG ⊔ SimpleGraph.edge a b) ⊕g FH).Reachable
              (Sum.inl u) (Sum.inl v) ↔
            (F.1 ⊔ SimpleGraph.edge (Sum.inl a) (Sum.inl b)).Reachable
              (Sum.inl u) (Sum.inl v) := by rw [hsup]
      rw [← reachable_sum_inl_iff (G := FG ⊔ SimpleGraph.edge a b)
        (H := FH) u v, hdecomp, F.2.2.2.2]
      exact reachable_sum_inl_iff u v
    · intro u v huv
      exact F.2.1 huv
    · exact F.2.2.1.of_comap ⟨Sum.inr, Sum.inr_injective⟩
    · ext u v
      have hdecomp :
          ((FG ⊔ SimpleGraph.edge a b) ⊕g FH).Reachable
              (Sum.inr u) (Sum.inr v) ↔
            (F.1 ⊔ SimpleGraph.edge (Sum.inl a) (Sum.inl b)).Reachable
              (Sum.inr u) (Sum.inr v) := by rw [hsup]
      rw [← reachable_sum_inr_iff (G := FG ⊔ SimpleGraph.edge a b)
        (H := FH) u v, hdecomp, F.2.2.2.2]
      exact reachable_sum_inr_iff u v
  invFun F := by
    refine ⟨F.1.1 ⊕g F.2.1, ?_, ?_, ?_, ?_⟩
    · intro x y hxy
      rcases x with x | x <;> rcases y with y | y
      · exact F.1.2.1 hxy
      · simp at hxy
      · simp at hxy
      · exact F.2.2.1 hxy
    · exact isAcyclic_sum F.1.2.2.1 F.2.2.2.1
    · rw [reachable_sum_inl_iff]
      exact F.1.2.2.2.1
    · have hsup := sup_edge_inl_sum_comap_eq
          (G := G) (H := H) (K := F.1.1 ⊕g F.2.1)
          (by
            intro x y hxy
            rcases x with x | x <;> rcases y with y | y
            · exact F.1.2.1 hxy
            · simp at hxy
            · simp at hxy
            · exact F.2.2.1 hxy)
          a b
      rw [← hsup]
      ext x y
      rcases x with x | x <;> rcases y with y | y
      · rw [reachable_sum_inl_iff, reachable_sum_inl_iff]
        change (F.1.1 ⊔ SimpleGraph.edge a b).Reachable x y ↔
          G.Reachable x y
        rw [F.1.2.2.2.2]
      · constructor
        · exact fun h ↦ (SimpleGraph.not_reachable_sum_inl_inr x y h).elim
        · exact fun h ↦ (SimpleGraph.not_reachable_sum_inl_inr x y h).elim
      · constructor
        · exact fun h ↦
            (SimpleGraph.not_reachable_sum_inl_inr y x h.symm).elim
        · exact fun h ↦
            (SimpleGraph.not_reachable_sum_inl_inr y x h.symm).elim
      · rw [reachable_sum_inr_iff, reachable_sum_inr_iff]
        change F.2.1.Reachable x y ↔ H.Reachable x y
        rw [F.2.2.2.2]
  left_inv F := by
    apply Subtype.ext
    exact sum_comap_eq_of_le F.2.1
  right_inv F := by
    apply Prod.ext
    · apply Subtype.ext
      rfl
    · apply Subtype.ext
      rfl

/-- Separating two-forest counts multiply by the forest count of components
disjoint from the terminals. -/
theorem abTwoForestCount_sum_inl
    {V W : Type*} [Finite V] [Finite W]
    (G : SimpleGraph V) (H : SimpleGraph W) (a b : V) :
    abTwoForestCount (G ⊕g H) (Sum.inl a) (Sum.inl b) =
      abTwoForestCount G a b * spanningForestCount H := by
  rw [abTwoForestCount, abTwoForestCount, spanningForestCount,
    Nat.card_congr (abTwoForestSumEquiv G H a b), Nat.card_prod]

private noncomputable def relabelGraphIso
    {V W : Type*} (e : V ≃ W) (G : SimpleGraph V) :
    G ≃g e.simpleGraph G where
  toEquiv := e
  map_rel_iff' := by
    intro u v
    simp

private theorem relabel_reachable
    {V W : Type*} (e : V ≃ W) (G : SimpleGraph V) (u v : V) :
    (e.simpleGraph G).Reachable (e u) (e v) ↔ G.Reachable u v := by
  exact (relabelGraphIso e G).reachable_iff

private theorem relabel_sup_edge
    {V W : Type*} (e : V ≃ W) (G : SimpleGraph V) (a b : V) :
    e.simpleGraph (G ⊔ SimpleGraph.edge a b) =
      e.simpleGraph G ⊔ SimpleGraph.edge (e a) (e b) := by
  ext u v
  simp only [Equiv.simpleGraph_apply, SimpleGraph.comap_adj,
    SimpleGraph.sup_adj, SimpleGraph.edge_adj]
  rw [Equiv.symm_apply_eq, Equiv.symm_apply_eq,
    Equiv.symm_apply_eq, Equiv.symm_apply_eq]
  rw [e.symm.injective.ne_iff]

/-- Maximal spanning forests are invariant under a graph isomorphism. -/
noncomputable def spanningForestEquivOfIso
    {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) : SpanningForestType G ≃ SpanningForestType H where
  toFun F := by
    let K : SimpleGraph W := e.toEquiv.simpleGraph F.1
    refine ⟨K, ?_, ?_, ?_⟩
    · intro u v huv
      change F.1.Adj (e.symm u) (e.symm v) at huv
      simpa only [e.apply_symm_apply] using e.map_rel_iff.mpr (F.2.1 huv)
    · exact (relabelGraphIso e.toEquiv F.1).isAcyclic_iff.mp F.2.2.1
    · ext u v
      change (e.toEquiv.simpleGraph F.1).Reachable u v ↔ H.Reachable u v
      let u' := e.symm u
      let v' := e.symm v
      have hF := relabel_reachable e.toEquiv F.1 u' v'
      have hG := e.reachable_iff (u := u') (v := v')
      have huF : e.toEquiv u' = u := e.apply_symm_apply u
      have hvF : e.toEquiv v' = v := e.apply_symm_apply v
      have huG : e u' = u := e.apply_symm_apply u
      have hvG : e v' = v := e.apply_symm_apply v
      rw [huF, hvF] at hF
      rw [huG, hvG] at hG
      have hEq : F.1.Reachable u' v' ↔ G.Reachable u' v' := by
        rw [F.2.2.2]
      exact hF.trans (hEq.trans hG.symm)
  invFun F := by
    let K : SimpleGraph V := e.symm.toEquiv.simpleGraph F.1
    refine ⟨K, ?_, ?_, ?_⟩
    · intro u v huv
      change F.1.Adj (e u) (e v) at huv
      exact e.map_rel_iff.mp (F.2.1 huv)
    · exact (relabelGraphIso e.symm.toEquiv F.1).isAcyclic_iff.mp F.2.2.1
    · ext u v
      change (e.symm.toEquiv.simpleGraph F.1).Reachable u v ↔ G.Reachable u v
      let u' := e u
      let v' := e v
      have hF := relabel_reachable e.symm.toEquiv F.1 u' v'
      have hG := e.reachable_iff (u := u) (v := v)
      have huF : e.symm.toEquiv u' = u := e.symm_apply_apply u
      have hvF : e.symm.toEquiv v' = v := e.symm_apply_apply v
      rw [huF, hvF] at hF
      have hEq : F.1.Reachable u' v' ↔ H.Reachable u' v' := by
        rw [F.2.2.2]
      exact hF.trans (hEq.trans hG)
  left_inv F := by
    apply Subtype.ext
    exact e.toEquiv.simpleGraph.symm_apply_apply F.1
  right_inv F := by
    apply Subtype.ext
    exact e.toEquiv.simpleGraph.apply_symm_apply F.1

/-- Separating two-forests are invariant under a graph isomorphism, with
the terminals transported by the isomorphism. -/
noncomputable def abTwoForestEquivOfIso
    {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) (a b : V) :
    ABTwoForestType G a b ≃ ABTwoForestType H (e a) (e b) where
  toFun F := by
    let K : SimpleGraph W := e.toEquiv.simpleGraph F.1
    refine ⟨K, ?_, ?_, ?_, ?_⟩
    · intro u v huv
      change F.1.Adj (e.symm u) (e.symm v) at huv
      simpa only [e.apply_symm_apply] using e.map_rel_iff.mpr (F.2.1 huv)
    · exact (relabelGraphIso e.toEquiv F.1).isAcyclic_iff.mp F.2.2.1
    · intro hab
      have hreach := relabel_reachable e.toEquiv F.1 a b
      exact F.2.2.2.1 (hreach.mp hab)
    · change (e.toEquiv.simpleGraph F.1 ⊔
          SimpleGraph.edge (e a) (e b)).Reachable = H.Reachable
      have hsup : e.toEquiv.simpleGraph (F.1 ⊔ SimpleGraph.edge a b) =
          e.toEquiv.simpleGraph F.1 ⊔ SimpleGraph.edge (e a) (e b) := by
        simpa using relabel_sup_edge e.toEquiv F.1 a b
      rw [← hsup]
      ext u v
      let u' := e.symm u
      let v' := e.symm v
      have hF := relabel_reachable e.toEquiv
        (F.1 ⊔ SimpleGraph.edge a b) u' v'
      have hG := e.reachable_iff (u := u') (v := v')
      have huF : e.toEquiv u' = u := e.apply_symm_apply u
      have hvF : e.toEquiv v' = v := e.apply_symm_apply v
      have huG : e u' = u := e.apply_symm_apply u
      have hvG : e v' = v := e.apply_symm_apply v
      rw [huF, hvF] at hF
      rw [huG, hvG] at hG
      have hEq : (F.1 ⊔ SimpleGraph.edge a b).Reachable u' v' ↔
          G.Reachable u' v' := by
        rw [F.2.2.2.2]
      exact hF.trans (hEq.trans hG.symm)
  invFun F := by
    let K : SimpleGraph V := e.symm.toEquiv.simpleGraph F.1
    refine ⟨K, ?_, ?_, ?_, ?_⟩
    · intro u v huv
      change F.1.Adj (e u) (e v) at huv
      exact e.map_rel_iff.mp (F.2.1 huv)
    · exact (relabelGraphIso e.symm.toEquiv F.1).isAcyclic_iff.mp F.2.2.1
    · intro hab
      change (e.symm.toEquiv.simpleGraph F.1).Reachable a b at hab
      have hreach := relabel_reachable e.symm.toEquiv F.1 (e a) (e b)
      have ha : e.symm.toEquiv (e a) = a := e.symm_apply_apply a
      have hb : e.symm.toEquiv (e b) = b := e.symm_apply_apply b
      rw [ha, hb] at hreach
      apply F.2.2.2.1
      exact hreach.mp hab
    · change (e.symm.toEquiv.simpleGraph F.1 ⊔
          SimpleGraph.edge a b).Reachable = G.Reachable
      have hsup : e.symm.toEquiv.simpleGraph
            (F.1 ⊔ SimpleGraph.edge (e a) (e b)) =
          e.symm.toEquiv.simpleGraph F.1 ⊔ SimpleGraph.edge a b := by
        have h := relabel_sup_edge e.symm.toEquiv F.1 (e a) (e b)
        have ha : e.symm.toEquiv (e a) = a := e.symm_apply_apply a
        have hb : e.symm.toEquiv (e b) = b := e.symm_apply_apply b
        rw [ha, hb] at h
        exact h
      rw [← hsup]
      ext u v
      let u' := e u
      let v' := e v
      have hF := relabel_reachable e.symm.toEquiv
        (F.1 ⊔ SimpleGraph.edge (e a) (e b)) u' v'
      have hG := e.reachable_iff (u := u) (v := v)
      have huF : e.symm.toEquiv u' = u := e.symm_apply_apply u
      have hvF : e.symm.toEquiv v' = v := e.symm_apply_apply v
      rw [huF, hvF] at hF
      have hEq : (F.1 ⊔ SimpleGraph.edge (e a) (e b)).Reachable u' v' ↔
          H.Reachable u' v' := by
        rw [F.2.2.2.2]
      exact hF.trans (hEq.trans hG)
  left_inv F := by
    apply Subtype.ext
    exact e.toEquiv.simpleGraph.symm_apply_apply F.1
  right_inv F := by
    apply Subtype.ext
    exact e.toEquiv.simpleGraph.apply_symm_apply F.1

theorem spanningForestCount_iso
    {V W : Type*} [Finite V] [Finite W]
    {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H) :
    spanningForestCount G = spanningForestCount H := by
  rw [spanningForestCount, spanningForestCount,
    Nat.card_congr (spanningForestEquivOfIso e)]

theorem abTwoForestCount_iso
    {V W : Type*} [Finite V] [Finite W]
    {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) (a b : V) :
    abTwoForestCount G a b = abTwoForestCount H (e a) (e b) := by
  rw [abTwoForestCount, abTwoForestCount,
    Nat.card_congr (abTwoForestEquivOfIso e a b)]

/-- Vertices outside the component reachable from `a`. -/
abbrev UnreachableVertex {V : Type*} (G : SimpleGraph V) (a : V) :=
  {v : V // ¬G.Reachable a v}

/-- The graph induced on the vertices outside the component of `a`. -/
def unreachableComponentGraph {V : Type*} (G : SimpleGraph V) (a : V) :
    SimpleGraph (UnreachableVertex G a) :=
  G.comap Subtype.val

/-- The component of `a` and its complement form a disjoint graph sum
isomorphic to the original graph. -/
noncomputable def reachablePartitionIso
    {V : Type*} (G : SimpleGraph V) (a : V) :
    reachableComponentGraph G a ⊕g unreachableComponentGraph G a ≃g G := by
  classical
  exact
    { toEquiv := Equiv.sumCompl fun v ↦ G.Reachable a v
      map_rel_iff' := by
        rintro (u | u) (v | v)
        · simp only [Equiv.sumCompl_apply_inl]
          rfl
        · simp only [Equiv.sumCompl_apply_inl, Equiv.sumCompl_apply_inr]
          constructor
          · intro huv
            exact u.2.trans huv.reachable |> v.2 |> False.elim
          · intro h
            simp at h
        · simp only [Equiv.sumCompl_apply_inr, Equiv.sumCompl_apply_inl]
          constructor
          · intro huv
            exact v.2.trans huv.symm.reachable |> u.2 |> False.elim
          · intro h
            simp at h
        · simp only [Equiv.sumCompl_apply_inr]
          rfl }

/-- Components disjoint from `a,b` cancel exactly from the two-forest
ratio.  This is the componentwise bridge needed because a words-on-a-page
prefix retains every future vertex as an isolated vertex. -/
theorem twoForestResistance_eq_reachableComponent
    {V : Type*} [Fintype V] (G : SimpleGraph V) (a b : V)
    (habReach : G.Reachable a b) :
    twoForestResistance G a b =
      twoForestResistance (reachableComponentGraph G a)
        ⟨a, SimpleGraph.Reachable.refl a⟩ ⟨b, habReach⟩ := by
  classical
  let a' : ReachableVertex G a :=
    ⟨a, SimpleGraph.Reachable.refl a⟩
  let b' : ReachableVertex G a := ⟨b, habReach⟩
  let U := unreachableComponentGraph G a
  let e := reachablePartitionIso G a
  change twoForestResistance G a b =
    twoForestResistance (reachableComponentGraph G a) a' b'
  have hea : e (Sum.inl a') = a := by
    simp [e, reachablePartitionIso, a']
  have heb : e (Sum.inl b') = b := by
    simp [e, reachablePartitionIso, b']
  have hden : spanningForestCount G =
      spanningForestCount (reachableComponentGraph G a) *
        spanningForestCount U := by
    calc
      spanningForestCount G =
          spanningForestCount
            (reachableComponentGraph G a ⊕g U) :=
        (spanningForestCount_iso e).symm
      _ = _ := spanningForestCount_sum _ _
  have hnum : abTwoForestCount G a b =
      abTwoForestCount (reachableComponentGraph G a) a' b' *
        spanningForestCount U := by
    calc
      abTwoForestCount G a b =
          abTwoForestCount
            (reachableComponentGraph G a ⊕g U)
              (Sum.inl a') (Sum.inl b') := by
        have h := abTwoForestCount_iso e (Sum.inl a') (Sum.inl b')
        rw [hea, heb] at h
        exact h.symm
      _ = _ := abTwoForestCount_sum_inl _ _ _ _
  have hU : (spanningForestCount U : ℝ) ≠ 0 := by
    exact_mod_cast (spanningForestCount_pos U).ne'
  unfold twoForestResistance
  rw [hnum, hden]
  push_cast
  field_simp

/-- Rayleigh monotonicity for a possibly disconnected source graph.  Only
the component containing the terminals is retained; all other components
cancel by `twoForestResistance_eq_reachableComponent`. -/
theorem twoForestResistance_antitone_embedding_reachable
    (hMatrixTree : LabeledMultigraphCofactorInput.{0, 0})
    {V W : Type} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W}
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (e : InjectiveGraphHom G H) (hH : H.Connected)
    (a b : V) (hab : a ≠ b) (habReach : G.Reachable a b)
    (hGnotadj : ¬G.Adj a b)
    (hHnotadj : ¬H.Adj (e.toEmbedding a) (e.toEmbedding b)) :
    twoForestResistance H (e.toEmbedding a) (e.toEmbedding b) ≤
      twoForestResistance G a b := by
  classical
  let a' : ReachableVertex G a :=
    ⟨a, SimpleGraph.Reachable.refl a⟩
  let b' : ReachableVertex G a := ⟨b, habReach⟩
  let ec := e.restrictReachableComponent a
  have hab' : a' ≠ b' := by
    intro h
    exact hab (congrArg Subtype.val h)
  have hnotadj' : ¬(reachableComponentGraph G a).Adj a' b' := by
    exact hGnotadj
  calc
    twoForestResistance H (e.toEmbedding a) (e.toEmbedding b) =
        twoForestResistance H (ec.toEmbedding a') (ec.toEmbedding b') := rfl
    _ ≤ twoForestResistance (reachableComponentGraph G a) a' b' :=
      twoForestResistance_antitone_embedding
        (twoForestCofactorInput_of_matrixTree hMatrixTree)
        ec (reachableComponentGraph_connected G a) hH
        a' b' hab' hnotadj' hHnotadj
    _ = twoForestResistance G a b :=
      (twoForestResistance_eq_reachableComponent G a b habReach).symm

/-- Restrict both sides of an embedding to the components of corresponding
terminals. -/
def InjectiveGraphHom.restrictReachableComponents
    {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (e : InjectiveGraphHom G H) (a : V) :
    InjectiveGraphHom (reachableComponentGraph G a)
      (reachableComponentGraph H (e.toEmbedding a)) where
  toEmbedding :=
    { toFun := fun v ↦
        ⟨e.toEmbedding v.1, v.2.map
          { toFun := e.toEmbedding
            map_rel' := fun hadj ↦ e.map_adj hadj }⟩
      inj' := by
        intro u v huv
        apply Subtype.ext
        exact e.toEmbedding.injective (congrArg Subtype.val huv) }
  map_adj := fun huv ↦ e.map_adj huv

/-- Fully componentwise Rayleigh monotonicity: neither ambient graph need
be connected, provided its two displayed terminals lie in one component.
Unrelated components cancel on both sides. -/
theorem twoForestResistance_antitone_embedding_components
    (hMatrixTree : LabeledMultigraphCofactorInput.{0, 0})
    {V W : Type} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W}
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (e : InjectiveGraphHom G H)
    (a b : V) (hab : a ≠ b)
    (hGReach : G.Reachable a b)
    (hHReach : H.Reachable (e.toEmbedding a) (e.toEmbedding b))
    (hGnotadj : ¬G.Adj a b)
    (hHnotadj : ¬H.Adj (e.toEmbedding a) (e.toEmbedding b)) :
    twoForestResistance H (e.toEmbedding a) (e.toEmbedding b) ≤
      twoForestResistance G a b := by
  classical
  let aG : ReachableVertex G a := ⟨a, SimpleGraph.Reachable.refl a⟩
  let bG : ReachableVertex G a := ⟨b, hGReach⟩
  let aH : ReachableVertex H (e.toEmbedding a) :=
    ⟨e.toEmbedding a, SimpleGraph.Reachable.refl _⟩
  let bH : ReachableVertex H (e.toEmbedding a) :=
    ⟨e.toEmbedding b, hHReach⟩
  let ec := e.restrictReachableComponents a
  have habG : aG ≠ bG := fun h ↦ hab (congrArg Subtype.val h)
  have hGnotadj' : ¬(reachableComponentGraph G a).Adj aG bG := hGnotadj
  have hHnotadj' : ¬(reachableComponentGraph H (e.toEmbedding a)).Adj
      aH bH := hHnotadj
  calc
    twoForestResistance H (e.toEmbedding a) (e.toEmbedding b) =
        twoForestResistance (reachableComponentGraph H (e.toEmbedding a))
          aH bH := twoForestResistance_eq_reachableComponent H
            (e.toEmbedding a) (e.toEmbedding b) hHReach
    _ = twoForestResistance (reachableComponentGraph H (e.toEmbedding a))
          (ec.toEmbedding aG) (ec.toEmbedding bG) := rfl
    _ ≤ twoForestResistance (reachableComponentGraph G a) aG bG :=
      twoForestResistance_antitone_embedding
        (twoForestCofactorInput_of_matrixTree hMatrixTree)
        ec (reachableComponentGraph_connected G a)
        (reachableComponentGraph_connected H (e.toEmbedding a))
        aG bG habG hGnotadj' hHnotadj'
    _ = twoForestResistance G a b :=
      (twoForestResistance_eq_reachableComponent G a b hGReach).symm

private theorem mem_wordsPrefixVertices_of_reachable
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    (coord : V ↪ Boundary.LatticePoint) (k : ℕ) {a v : V}
    (ha : a ∈ wordsPrefixVertices coord k)
    (hav : (wordsPrefixGraph G coord k).Reachable a v) :
    v ∈ wordsPrefixVertices coord k := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at hav
  induction hav with
  | refl => exact ha
  | @tail y z _ hyz ih => exact hyz.2.2

private noncomputable def reachableComponentToPrefixVertex
    {V : Type} [Fintype V] (G : SimpleGraph V)
    (coord : V ↪ Boundary.LatticePoint) (k : ℕ) (a : V)
    (ha : a ∈ wordsPrefixVertices coord k) :
    InjectiveGraphHom
      (reachableComponentGraph (wordsPrefixGraph G coord k) a)
      (prefixVertexGraph G coord k) where
  toEmbedding :=
    { toFun := fun v ↦
        ⟨v.1, mem_wordsPrefixVertices_of_reachable G coord k ha v.2⟩
      inj' := by
        intro u v h
        apply Subtype.ext
        exact congrArg (fun q : PrefixVertex coord k ↦ q.1) h }
  map_adj := fun huv ↦ huv

/-- The terminal component of an arbitrary finite prefix embeds in any
canonical half-plane window containing all ambient coordinates. -/
noncomputable def reachablePrefixGraphHomToHalfPlaneWindow
    {V : Type} [Fintype V] (G : SimpleGraph V)
    (coord : V ↪ Boundary.LatticePoint)
    (k : ℕ) (hk : k < Fintype.card V) (z : Boundary.LatticePoint)
    (hLattice : G ≤ Boundary.faceLattice.comap coord)
    (hcoord : coord ((wordsOnPageOrderIso coord).toEquiv ⟨k, hk⟩) =
      (z.1 + 1, z.2))
    (X Y : ℕ) (hX : ∀ v, (coord v).1 < X)
    (hY : ∀ v, (coord v).2 < Y)
    (a : V) (ha : a ∈ wordsPrefixVertices coord k) :
    InjectiveGraphHom
      (reachableComponentGraph (wordsPrefixGraph G coord k) a)
      (halfPlaneWindowGraph z X Y) := by
  let ep := reachableComponentToPrefixVertex G coord k a ha
  let ew := prefixGraphHomToHalfPlaneWindow G coord k hk z hLattice hcoord
    X Y hX hY
  exact
    { toEmbedding := ep.toEmbedding.trans ew.toEmbedding
      map_adj := fun huv ↦ ew.map_adj (ep.map_adj huv) }

private theorem faceLattice_not_adj_diagonal (z : Boundary.LatticePoint) :
    ¬Boundary.faceLattice.Adj z (z.1 + 1, z.2 + 1) := by
  simp [Boundary.faceLattice, Boundary.natManhattanDist, Nat.dist]

/-- The canonical finite-window lower bound implies the original
words-on-a-page half-plane estimate.  This theorem contains the corrected
Rayleigh direction: the terminal component of the prefix embeds into the
larger canonical window, hence window resistance is no larger. -/
theorem halfPlaneTwoForestResistanceBound_of_canonical
    (hMatrixTree : LabeledMultigraphCofactorInput.{0, 0})
    {κ : ℝ} (hcanonical : CanonicalHalfPlaneMultiplierLowerBound κ) :
    HalfPlaneTwoForestResistanceBound κ := by
  intro V _ G coord k hk z hLattice hsquare hcoord
  classical
  let sw := unitSquareSWVertex hsquare
  let ne := unitSquareNECornerVertex hsquare
  let P := wordsPrefixGraph G coord k
  have hswMem : sw ∈ wordsPrefixVertices coord k := by
    apply mem_wordsPrefixVertices_of_key_lt coord k hk
    rw [unitSquareSWVertex_coord hsquare, hcoord]
    rw [wordsOnPageKey, wordsOnPageKey, Prod.Lex.toLex_lt_toLex]
    exact Or.inr ⟨rfl, by omega⟩
  have hneMem : ne ∈ wordsPrefixVertices coord k := by
    apply mem_wordsPrefixVertices_of_key_lt coord k hk
    rw [unitSquareNECornerVertex_coord hsquare, hcoord]
    rw [wordsOnPageKey, wordsOnPageKey, Prod.Lex.toLex_lt_toLex]
    left
    omega
  have hreach : P.Reachable sw ne := by
    exact wordsPrefixGraph_square_neighbors_reachable
      coord k hk z hsquare hcoord
  obtain ⟨X, Y, hx, hy, hX, hY⟩ :=
    exists_halfPlaneWindow_coordinate_bounds coord z
  let e := reachablePrefixGraphHomToHalfPlaneWindow
    G coord k hk z hLattice hcoord X Y hX hY sw hswMem
  let sw' : ReachableVertex P sw := ⟨sw, SimpleGraph.Reachable.refl sw⟩
  let ne' : ReachableVertex P sw := ⟨ne, hreach⟩
  have hesw : e.toEmbedding sw' =
      halfPlaneWindowSW z X Y (by omega) (by omega) := by
    apply Subtype.ext
    exact unitSquareSWVertex_coord hsquare
  have hene : e.toEmbedding ne' = halfPlaneWindowNE z X Y hx hy := by
    apply Subtype.ext
    exact unitSquareNECornerVertex_coord hsquare
  have hswne : sw ≠ ne := by
    intro h
    have hc := congrArg coord h
    rw [unitSquareSWVertex_coord hsquare,
      unitSquareNECornerVertex_coord hsquare] at hc
    have hxcoord := congrArg Prod.fst hc
    simp only at hxcoord
    omega
  have hPnotadj : ¬P.Adj sw ne := by
    intro hadj
    have hlat := hLattice hadj.1
    change Boundary.faceLattice.Adj (coord sw) (coord ne) at hlat
    dsimp only [sw, ne] at hlat
    rw [unitSquareSWVertex_coord hsquare,
      unitSquareNECornerVertex_coord hsquare] at hlat
    exact faceLattice_not_adj_diagonal z hlat
  have hWnotadj : ¬(halfPlaneWindowGraph z X Y).Adj
      (e.toEmbedding sw') (e.toEmbedding ne') := by
    rw [hesw, hene]
    intro hadj
    exact faceLattice_not_adj_diagonal z hadj
  have hray : twoForestResistance (halfPlaneWindowGraph z X Y)
        (halfPlaneWindowSW z X Y (by omega) (by omega))
        (halfPlaneWindowNE z X Y hx hy) ≤
      twoForestResistance P sw ne := by
    calc
      twoForestResistance (halfPlaneWindowGraph z X Y)
          (halfPlaneWindowSW z X Y (by omega) (by omega))
          (halfPlaneWindowNE z X Y hx hy) =
          twoForestResistance (halfPlaneWindowGraph z X Y)
            (e.toEmbedding sw') (e.toEmbedding ne') := by rw [hesw, hene]
      _ ≤ twoForestResistance (reachableComponentGraph P sw) sw' ne' :=
        twoForestResistance_antitone_embedding
          (twoForestCofactorInput_of_matrixTree hMatrixTree)
          e (reachableComponentGraph_connected P sw)
          (halfPlaneWindowGraph_connected z X Y hx hy)
          sw' ne' (by exact fun h ↦ hswne (congrArg Subtype.val h))
          hPnotadj hWnotadj
      _ = twoForestResistance P sw ne :=
        (twoForestResistance_eq_reachableComponent P sw ne hreach).symm
  have hwindow := hcanonical z X Y hx hy
  dsimp only [P, sw, ne] at hray ⊢
  linarith

end Dual
end SquareMaximality
