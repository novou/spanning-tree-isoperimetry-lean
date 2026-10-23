module

public import SquareMaximality.Dual.TappResistance
public import SquareMaximality.Boundary.TraceWalks

@[expose] public section

set_option backward.privateInPublic true

/-!
# The two-forest series-extension identity

This module lowers the remaining local input in `TappResistance.lean` from a
prefix multiplier inequality to the conventional two-forest ratio.  The
finite identity proved here is the deterministic series-extension step in
Tapp's Proposition 5.2: adjoining a new degree-two vertex between vertices
`a` and `b` multiplies the spanning-forest product by

`2 + (# separating two-forests) / (# spanning forests)`.

The eventual analytic input is therefore only the Rayleigh/half-plane lower
bound for this genuine two-forest ratio.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace SquareMaximality
namespace Dual

open scoped BigOperators

/-! ## The degree-two extension -/

/-- Add a new degree-two vertex `v` with neighbours `a,b`. -/
def seriesExtension {V : Type*} (P : SimpleGraph V) (v a b : V) :
    SimpleGraph V :=
  P ⊔ SimpleGraph.edge v a ⊔ SimpleGraph.edge v b

/-! ## Reachability helpers -/

/-- Replace `v` by `a`, fixing every other vertex. -/
private def foldVertex {V : Type*} [DecidableEq V] (v a : V) (x : V) : V :=
  if x = v then a else x

private theorem reachable_eq_of_le_of_adj_reachable
    {V : Type*} {S Q : SimpleGraph V} (hSQ : S ≤ Q)
    (h : ∀ x y, Q.Adj x y → S.Reachable x y) :
    S.Reachable = Q.Reachable := by
  funext x y
  apply propext
  constructor
  · exact SimpleGraph.Reachable.mono hSQ
  · rw [SimpleGraph.reachable_iff_reflTransGen,
      SimpleGraph.reachable_iff_reflTransGen]
    intro hxy
    have hlift := Relation.ReflTransGen.lift'
      (r := Q.Adj) (p := S.Adj) id (fun x y hxy ↦
        (SimpleGraph.reachable_iff_reflTransGen x y).mp (h x y hxy))
    exact hlift x y hxy

private theorem reachable_of_adj_reachable
    {V : Type*} {G H : SimpleGraph V}
    (h : ∀ x y, G.Adj x y → H.Reachable x y) :
    G.Reachable ≤ H.Reachable := by
  intro x y hxy
  rw [SimpleGraph.reachable_iff_reflTransGen] at hxy
  rw [SimpleGraph.reachable_iff_reflTransGen]
  have hlift := Relation.ReflTransGen.lift'
    (r := G.Adj) (p := H.Adj) id (fun p q hpq ↦
      (SimpleGraph.reachable_iff_reflTransGen p q).mp (h p q hpq))
  exact hlift x y hxy

/-- Folding the leaf edge `v-a` sends reachability back to the old graph.
The edge itself folds to a reflexive step. -/
private theorem reachable_fold_sup_edge
    {V : Type*} [DecidableEq V] {P : SimpleGraph V} {v a x y : V}
    (hva : v ≠ a) (hv : P.IsIsolated v)
    (hxy : (P ⊔ SimpleGraph.edge v a).Reachable x y) :
    P.Reachable (foldVertex v a x) (foldVertex v a y) := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at hxy ⊢
  exact hxy.lift' (foldVertex v a) fun p q hpq ↦ by
    rw [SimpleGraph.sup_adj] at hpq
    rcases hpq with hpq | hpq
    · have hpv : p ≠ v := fun hpv ↦ hv q (hpv ▸ hpq)
      have hqv : q ≠ v := fun hqv ↦ hv p (hqv ▸ hpq.symm)
      exact (SimpleGraph.reachable_iff_reflTransGen _ _).mp <| by
        simpa [foldVertex, hpv, hqv] using hpq.reachable
    · rw [SimpleGraph.edge_adj] at hpq
      rcases hpq with ⟨hpv, hqa⟩ | ⟨hpa, hqv⟩
      · rw [hpv, hqa]
        simpa [Function.onFun, foldVertex, hva, hva.symm] using
          (Relation.ReflTransGen.refl :
            Relation.ReflTransGen P.Adj a a)
      · rw [hpa, hqv]
        simpa [Function.onFun, foldVertex, hva, hva.symm] using
          (Relation.ReflTransGen.refl :
            Relation.ReflTransGen P.Adj a a)

/-- Replace the abstract edge `a-b` by the two-edge path `a-v-b`. -/
private theorem reachable_replace_edge_by_series
    {V : Type*} {F : SimpleGraph V} {v a b x y : V}
    (hva : v ≠ a) (hvb : v ≠ b)
    (hxy : (F ⊔ SimpleGraph.edge a b).Reachable x y) :
    (seriesExtension F v a b).Reachable x y := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at hxy ⊢
  have habSeries : (seriesExtension F v a b).Reachable a b := by
    have hav : (seriesExtension F v a b).Adj a v := by
      simp only [seriesExtension, SimpleGraph.sup_adj]
      left
      right
      rw [SimpleGraph.edge_adj]
      exact ⟨Or.inr ⟨rfl, rfl⟩, hva.symm⟩
    have hvb' : (seriesExtension F v a b).Adj v b := by
      simp only [seriesExtension, SimpleGraph.sup_adj]
      right
      rw [SimpleGraph.edge_adj]
      exact ⟨Or.inl ⟨rfl, rfl⟩, hvb⟩
    exact hav.reachable.trans hvb'.reachable
  have hlift := Relation.ReflTransGen.lift'
    (r := (F ⊔ SimpleGraph.edge a b).Adj)
    (p := (seriesExtension F v a b).Adj) id (fun p q hpq ↦ by
      rw [SimpleGraph.sup_adj] at hpq
      rcases hpq with hFpq | habpq
      · exact (SimpleGraph.reachable_iff_reflTransGen _ _).mp <|
          (show (seriesExtension F v a b).Adj p q by
            simp only [seriesExtension, SimpleGraph.sup_adj]
            exact Or.inl (Or.inl hFpq)).reachable
      · rw [SimpleGraph.edge_adj] at habpq
        rcases habpq with ⟨⟨rfl, rfl⟩ | ⟨rfl, rfl⟩, _⟩
        · exact (SimpleGraph.reachable_iff_reflTransGen _ _).mp habSeries
        · exact (SimpleGraph.reachable_iff_reflTransGen _ _).mp habSeries.symm)
  exact hlift x y hxy

/-- Folding the new vertex in the degree-two extension replaces its two
incident edges by the single edge `a-b`. -/
private theorem reachable_fold_seriesExtension
    {V : Type*} [DecidableEq V] {F : SimpleGraph V} {v a b x y : V}
    (hva : v ≠ a) (hvb : v ≠ b) (hab : a ≠ b)
    (hv : F.IsIsolated v)
    (hxy : (seriesExtension F v a b).Reachable x y) :
    (F ⊔ SimpleGraph.edge a b).Reachable
      (foldVertex v a x) (foldVertex v a y) := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at hxy ⊢
  have hlift := Relation.ReflTransGen.lift'
    (r := (seriesExtension F v a b).Adj)
    (p := (F ⊔ SimpleGraph.edge a b).Adj) (foldVertex v a)
    (fun p q hpq ↦ by
      simp only [seriesExtension, SimpleGraph.sup_adj] at hpq
      rcases hpq with (hFpq | hvapq) | hvbpq
      · have hpv : p ≠ v := fun hpv ↦ hv q (hpv ▸ hFpq)
        have hqv : q ≠ v := fun hqv ↦ hv p (hqv ▸ hFpq.symm)
        apply (SimpleGraph.reachable_iff_reflTransGen _ _).mp
        simpa [foldVertex, hpv, hqv] using
          (show (F ⊔ SimpleGraph.edge a b).Adj p q by
            exact Or.inl hFpq).reachable
      · rw [SimpleGraph.edge_adj] at hvapq
        rcases hvapq with ⟨⟨hpv, hqa⟩ | ⟨hpa, hqv⟩, _⟩
        · rw [hpv, hqa]
          simpa [Function.onFun, foldVertex, hva, hva.symm] using
            (Relation.ReflTransGen.refl :
              Relation.ReflTransGen (F ⊔ SimpleGraph.edge a b).Adj a a)
        · rw [hpa, hqv]
          simpa [Function.onFun, foldVertex, hva, hva.symm] using
            (Relation.ReflTransGen.refl :
              Relation.ReflTransGen (F ⊔ SimpleGraph.edge a b).Adj a a)
      · rw [SimpleGraph.edge_adj] at hvbpq
        rcases hvbpq with ⟨⟨hpv, hqb⟩ | ⟨hpb, hqv⟩, _⟩
        · rw [hpv, hqb]
          apply (SimpleGraph.reachable_iff_reflTransGen _ _).mp
          simpa [Function.onFun, foldVertex, hva, hvb, hvb.symm] using
            (show (F ⊔ SimpleGraph.edge a b).Adj a b by
              apply Or.inr
              rw [SimpleGraph.edge_adj]
              exact ⟨Or.inl ⟨rfl, rfl⟩, hab⟩).reachable
        · rw [hpb, hqv]
          apply (SimpleGraph.reachable_iff_reflTransGen _ _).mp
          simpa [Function.onFun, foldVertex, hva, hvb, hvb.symm] using
            (show (F ⊔ SimpleGraph.edge a b).Adj b a by
              apply Or.inr
              rw [SimpleGraph.edge_adj]
              exact ⟨Or.inr ⟨rfl, rfl⟩, hab.symm⟩).reachable)
  exact hlift x y hxy

/-! ## Two-forests and the degree-two extension -/

/-- A separating `a-b` two-forest in `P`.

It is acyclic, lies in `P`, separates `a` from `b`, and adding the missing
`a-b` edge restores exactly the component relation of `P`.  Thus all other
components remain spanning trees and the component of `a,b` is split into
exactly two trees. -/
def IsABTwoForest {V : Type*} (P F : SimpleGraph V) (a b : V) : Prop :=
  F ≤ P ∧ F.IsAcyclic ∧ ¬ F.Reachable a b ∧
    (F ⊔ SimpleGraph.edge a b).Reachable = P.Reachable

/-- Finite type of separating two-forests. -/
abbrev ABTwoForestType {V : Type*} (P : SimpleGraph V) (a b : V) :=
  {F : SimpleGraph V // IsABTwoForest P F a b}

/-- Number of separating `a-b` two-forests. -/
noncomputable def abTwoForestCount {V : Type*} [Finite V]
    (P : SimpleGraph V) (a b : V) : ℕ :=
  Nat.card (ABTwoForestType P a b)

/-- The unit-conductance effective resistance, in its all-minors
Matrix--Tree/two-forest form. -/
noncomputable def twoForestResistance {V : Type*} [Finite V]
    (P : SimpleGraph V) (a b : V) : ℝ :=
  (abTwoForestCount P a b : ℝ) / spanningForestCount P

@[simp] theorem seriesExtension_swap {V : Type*} (P : SimpleGraph V)
    (v a b : V) :
    seriesExtension P v b a = seriesExtension P v a b := by
  simp only [seriesExtension]
  ac_rfl

private theorem isIsolated_of_le
    {V : Type*} {F P : SimpleGraph V} {v : V}
    (hFP : F ≤ P) (hv : P.IsIsolated v) : F.IsIsolated v := by
  intro w hvw
  exact hv w (hFP hvw)

private theorem edge_le_of_adj
    {V : Type*} {G : SimpleGraph V} {x y : V} (hxy : G.Adj x y) :
    SimpleGraph.edge x y ≤ G :=
  (SimpleGraph.edge_le_iff G).mpr (Or.inr hxy)

private theorem inf_edge_eq_bot_of_not_adj
    {V : Type*} {G : SimpleGraph V} {x y : V}
    (hxy : ¬ G.Adj x y) :
    G ⊓ SimpleGraph.edge x y = ⊥ := by
  apply le_antisymm
  · intro p q hpq
    rcases (SimpleGraph.edge_adj x y p q).mp hpq.2 with
      ⟨⟨rfl, rfl⟩ | ⟨rfl, rfl⟩, _⟩
    · exact (hxy hpq.1).elim
    · exact (hxy hpq.1.symm).elim
  · exact bot_le

private theorem spanningForest_reconstruct
    {V : Type*} {P : SimpleGraph V} {v a b : V}
    (T : SpanningForestType (seriesExtension P v a b)) :
    T.1 = (T.1 ⊓ P) ⊔ (T.1 ⊓ SimpleGraph.edge v a) ⊔
      (T.1 ⊓ SimpleGraph.edge v b) := by
  calc
    T.1 = T.1 ⊓ seriesExtension P v a b :=
      (inf_eq_left.mpr T.2.1).symm
    _ = (T.1 ⊓ P) ⊔ (T.1 ⊓ SimpleGraph.edge v a) ⊔
        (T.1 ⊓ SimpleGraph.edge v b) := by
      simp only [seriesExtension, inf_sup_left]

private theorem spanningForest_reconstruct_left
    {V : Type*} {P : SimpleGraph V} {v a b : V}
    (T : SpanningForestType (seriesExtension P v a b))
    (hva : T.1.Adj v a) (hvb : ¬ T.1.Adj v b) :
    T.1 = (T.1 ⊓ P) ⊔ SimpleGraph.edge v a := by
  calc
    T.1 = (T.1 ⊓ P) ⊔ (T.1 ⊓ SimpleGraph.edge v a) ⊔
        (T.1 ⊓ SimpleGraph.edge v b) := spanningForest_reconstruct T
    _ = (T.1 ⊓ P) ⊔ SimpleGraph.edge v a := by
      rw [inf_eq_right.mpr (edge_le_of_adj hva),
        inf_edge_eq_bot_of_not_adj hvb, sup_bot_eq]

private theorem spanningForest_reconstruct_right
    {V : Type*} {P : SimpleGraph V} {v a b : V}
    (T : SpanningForestType (seriesExtension P v a b))
    (hva : ¬ T.1.Adj v a) (hvb : T.1.Adj v b) :
    T.1 = (T.1 ⊓ P) ⊔ SimpleGraph.edge v b := by
  calc
    T.1 = (T.1 ⊓ P) ⊔ (T.1 ⊓ SimpleGraph.edge v a) ⊔
        (T.1 ⊓ SimpleGraph.edge v b) := spanningForest_reconstruct T
    _ = (T.1 ⊓ P) ⊔ SimpleGraph.edge v b := by
      rw [inf_edge_eq_bot_of_not_adj hva, sup_bot_eq,
        inf_eq_right.mpr (edge_le_of_adj hvb)]

private theorem spanningForest_reconstruct_both
    {V : Type*} {P : SimpleGraph V} {v a b : V}
    (T : SpanningForestType (seriesExtension P v a b))
    (hva : T.1.Adj v a) (hvb : T.1.Adj v b) :
    T.1 = seriesExtension (T.1 ⊓ P) v a b := by
  calc
    T.1 = (T.1 ⊓ P) ⊔ (T.1 ⊓ SimpleGraph.edge v a) ⊔
        (T.1 ⊓ SimpleGraph.edge v b) := spanningForest_reconstruct T
    _ = seriesExtension (T.1 ⊓ P) v a b := by
      rw [inf_eq_right.mpr (edge_le_of_adj hva),
        inf_eq_right.mpr (edge_le_of_adj hvb)]
      rfl

private theorem adj_endpoint_of_edge_adj
    {V : Type*} {G : SimpleGraph V} {v a x y : V}
    (hG : G.Adj x y) (hEdge : (SimpleGraph.edge v a).Adj x y) :
    G.Adj v a := by
  rcases (SimpleGraph.edge_adj v a x y).mp hEdge with
    ⟨⟨rfl, rfl⟩ | ⟨rfl, rfl⟩, _⟩
  · exact hG
  · exact hG.symm

private theorem spanningForest_has_incident_edge
    {V : Type*} {P : SimpleGraph V} {v a b : V}
    (hva : v ≠ a) (hv : P.IsIsolated v)
    (T : SpanningForestType (seriesExtension P v a b)) :
    T.1.Adj v a ∨ T.1.Adj v b := by
  by_contra hnone
  push Not at hnone
  have hTiso : T.1.IsIsolated v := by
    intro x hvx
    have hQvx := T.2.1 hvx
    simp only [seriesExtension, SimpleGraph.sup_adj] at hQvx
    rcases hQvx with (hPvx | hvax) | hvbx
    · exact hv x hPvx
    · exact hnone.1 (adj_endpoint_of_edge_adj hvx hvax)
    · exact hnone.2 (adj_endpoint_of_edge_adj hvx hvbx)
  have hQva : (seriesExtension P v a b).Reachable v a := by
    apply SimpleGraph.Adj.reachable
    simp only [seriesExtension, SimpleGraph.sup_adj]
    left
    right
    rw [SimpleGraph.edge_adj]
    exact ⟨Or.inl ⟨rfl, rfl⟩, hva⟩
  have hTva : T.1.Reachable v a := by
    rw [T.2.2.2]
    exact hQva
  exact (SimpleGraph.not_reachable_of_neighborSet_left_eq_empty hva
    hTiso.neighborSet_eq_empty) hTva

/-- Restrict a one-edge extension back to the old spanning forest. -/
private noncomputable def spanningForestSingleRestrictionAux
    {V : Type*} [Fintype V] {P Q : SimpleGraph V} {v c : V}
    (hvc : v ≠ c) (hv : P.IsIsolated v) (hPQ : P ≤ Q)
    (T : SpanningForestType Q)
    (hreconstruct : T.1 = (T.1 ⊓ P) ⊔ SimpleGraph.edge v c) :
    SpanningForestType P := by
  classical
  let R := T.1 ⊓ P
  have hRiso : R.IsIsolated v := isIsolated_of_le inf_le_right hv
  refine ⟨R, inf_le_right, T.2.2.1.anti inf_le_left, ?_⟩
  apply reachable_eq_of_le_of_adj_reachable inf_le_right
  intro x y hPxy
  have hxv : x ≠ v := fun hxv ↦ hv y (hxv ▸ hPxy)
  have hyv : y ≠ v := fun hyv ↦ hv x (hyv ▸ hPxy.symm)
  have hTxy : T.1.Reachable x y := by
    rw [T.2.2.2]
    exact (hPQ hPxy).reachable
  rw [hreconstruct] at hTxy
  have hfold := reachable_fold_sup_edge hvc hRiso hTxy
  simpa [R, foldVertex, hxv, hyv] using hfold

private noncomputable def spanningForestLeftRestriction
    {V : Type*} [Fintype V] {P : SimpleGraph V} {v a b : V}
    (hva : v ≠ a) (hv : P.IsIsolated v)
    (T : SpanningForestType (seriesExtension P v a b))
    (hTa : T.1.Adj v a) (hTb : ¬ T.1.Adj v b) :
    SpanningForestType P :=
  spanningForestSingleRestrictionAux hva hv
    (le_sup_left.trans le_sup_left) T
    (spanningForest_reconstruct_left T hTa hTb)

private noncomputable def spanningForestRightRestriction
    {V : Type*} [Fintype V] {P : SimpleGraph V} {v a b : V}
    (hvb : v ≠ b) (hv : P.IsIsolated v)
    (T : SpanningForestType (seriesExtension P v a b))
    (hTa : ¬ T.1.Adj v a) (hTb : T.1.Adj v b) :
    SpanningForestType P :=
  spanningForestSingleRestrictionAux hvb hv
    (le_sup_left.trans le_sup_left) T
    (spanningForest_reconstruct_right T hTa hTb)

/-- Restrict a two-edge extension back to its separating two-forest. -/
private noncomputable def spanningForestDoubleRestriction
    {V : Type*} [Fintype V] {P : SimpleGraph V} {v a b : V}
    (hva : v ≠ a) (hvb : v ≠ b) (hab : a ≠ b)
    (hv : P.IsIsolated v) (hPab : P.Reachable a b)
    (T : SpanningForestType (seriesExtension P v a b))
    (hTa : T.1.Adj v a) (hTb : T.1.Adj v b) :
    ABTwoForestType P a b := by
  classical
  let R := T.1 ⊓ P
  let S₁ := R ⊔ SimpleGraph.edge v a
  have hRiso : R.IsIsolated v := isIsolated_of_le inf_le_right hv
  have hreconstruct : T.1 = seriesExtension R v a b :=
    spanningForest_reconstruct_both T hTa hTb
  have hnRab : ¬ R.Reachable a b := by
    intro hRab
    have hvaS₁ : S₁.Reachable v a := by
      apply SimpleGraph.Adj.reachable
      simp only [S₁, SimpleGraph.sup_adj]
      right
      rw [SimpleGraph.edge_adj]
      exact ⟨Or.inl ⟨rfl, rfl⟩, hva⟩
    have habS₁ : S₁.Reachable a b :=
      SimpleGraph.Reachable.mono le_sup_left hRab
    have hvbS₁ : S₁.Reachable v b := hvaS₁.trans habS₁
    have hS₁notAdj : ¬ S₁.Adj v b := by
      intro hAdj
      simp only [S₁, SimpleGraph.sup_adj] at hAdj
      rcases hAdj with hRvb | hvab
      · exact hRiso b hRvb
      · rcases (SimpleGraph.edge_adj v a v b).mp hvab with
          ⟨⟨_, hab'⟩ | ⟨hva', _⟩, _⟩
        · exact hab hab'.symm
        · exact hva hva'
    have hTacyclic : (S₁ ⊔ SimpleGraph.edge v b).IsAcyclic := by
      simpa [hreconstruct, seriesExtension, S₁] using T.2.2.1
    have hcriterion :=
      (SimpleGraph.isAcyclic_sup_fromEdgeSet_iff
        (G := S₁) (u := v) (v := b)).mp hTacyclic
    rcases hcriterion.2 hvbS₁ with hvbEq | hvbAdj
    · exact hvb hvbEq
    · exact hS₁notAdj hvbAdj
  have hreach : (R ⊔ SimpleGraph.edge a b).Reachable = P.Reachable := by
    apply le_antisymm
    · apply reachable_of_adj_reachable
      intro x y hxy
      simp only [SimpleGraph.sup_adj] at hxy
      rcases hxy with hRxy | habxy
      · exact (show P.Adj x y from hRxy.2).reachable
      · rcases (SimpleGraph.edge_adj a b x y).mp habxy with
          ⟨⟨rfl, rfl⟩ | ⟨rfl, rfl⟩, _⟩
        · exact hPab
        · exact hPab.symm
    · apply reachable_of_adj_reachable
      intro x y hPxy
      have hxv : x ≠ v := fun hxv ↦ hv y (hxv ▸ hPxy)
      have hyv : y ≠ v := fun hyv ↦ hv x (hyv ▸ hPxy.symm)
      have hTxy : T.1.Reachable x y := by
        rw [T.2.2.2]
        exact (show (seriesExtension P v a b).Adj x y by
          simp only [seriesExtension, SimpleGraph.sup_adj]
          exact Or.inl (Or.inl hPxy)).reachable
      rw [hreconstruct] at hTxy
      have hfold := reachable_fold_seriesExtension hva hvb hab hRiso hTxy
      simpa [foldVertex, hxv, hyv] using hfold
  exact ⟨R, inf_le_right, T.2.2.1.anti inf_le_left, hnRab, hreach⟩

/-- Attach the new vertex by only its first edge. -/
private noncomputable def spanningForestSingleExtension
    {V : Type*} [Fintype V] {P : SimpleGraph V} {v a b : V}
    (hva : v ≠ a) (hv : P.IsIsolated v) (hab : P.Reachable a b) :
    SpanningForestType P → SpanningForestType (seriesExtension P v a b) :=
  fun F ↦ by
    let S := F.1 ⊔ SimpleGraph.edge v a
    have hFiso : F.1.IsIsolated v := isIsolated_of_le F.2.1 hv
    have hnreach : ¬ F.1.Reachable v a :=
      SimpleGraph.not_reachable_of_neighborSet_left_eq_empty hva
        hFiso.neighborSet_eq_empty
    refine ⟨S, ?_, F.2.2.1.sup_edge_of_not_reachable hnreach, ?_⟩
    · exact sup_le
        (F.2.1.trans (le_sup_left.trans le_sup_left))
        (le_sup_right.trans le_sup_left)
    · apply reachable_eq_of_le_of_adj_reachable
        (sup_le
          (F.2.1.trans (le_sup_left.trans le_sup_left))
          (le_sup_right.trans le_sup_left))
      intro x y hxy
      simp only [SimpleGraph.sup_adj] at hxy
      rcases hxy with (hPxy | hvaxy) | hvbxy
      · have hFxy : F.1.Reachable x y := by
          rw [F.2.2.2]
          exact hPxy.reachable
        exact hFxy.mono le_sup_left
      · exact (show S.Adj x y from Or.inr hvaxy).reachable
      · have hvaS : S.Reachable v a := by
          apply SimpleGraph.Adj.reachable
          simp only [S, SimpleGraph.sup_adj]
          right
          rw [SimpleGraph.edge_adj]
          exact ⟨Or.inl ⟨rfl, rfl⟩, hva⟩
        have habS : S.Reachable a b := by
          apply SimpleGraph.Reachable.mono le_sup_left
          rw [F.2.2.2]
          exact hab
        rw [SimpleGraph.edge_adj] at hvbxy
        rcases hvbxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hvaS.trans habS
        · exact habS.symm.trans hvaS.symm

/-- The one-edge extension using the southeast vertex's west neighbour. -/
private noncomputable def spanningForestLeftExtension
    {V : Type*} [Fintype V] {P : SimpleGraph V} {v a b : V}
    (hva : v ≠ a) (hv : P.IsIsolated v) (hab : P.Reachable a b) :
    SpanningForestType P → SpanningForestType (seriesExtension P v a b) :=
  spanningForestSingleExtension hva hv hab

/-- The one-edge extension using the southeast vertex's north neighbour. -/
private noncomputable def spanningForestRightExtension
    {V : Type*} [Fintype V] {P : SimpleGraph V} {v a b : V}
    (hvb : v ≠ b) (hv : P.IsIsolated v) (hab : P.Reachable a b) :
    SpanningForestType P → SpanningForestType (seriesExtension P v a b) :=
  fun F ↦ by
    let S := F.1 ⊔ SimpleGraph.edge v b
    have hFiso : F.1.IsIsolated v := isIsolated_of_le F.2.1 hv
    have hnreach : ¬ F.1.Reachable v b :=
      SimpleGraph.not_reachable_of_neighborSet_left_eq_empty hvb
        hFiso.neighborSet_eq_empty
    have hSle : S ≤ seriesExtension P v a b :=
      sup_le (F.2.1.trans (le_sup_left.trans le_sup_left)) le_sup_right
    refine ⟨S, hSle, F.2.2.1.sup_edge_of_not_reachable hnreach, ?_⟩
    apply reachable_eq_of_le_of_adj_reachable hSle
    intro x y hxy
    simp only [seriesExtension, SimpleGraph.sup_adj] at hxy
    rcases hxy with (hPxy | hvaxy) | hvbxy
    · have hFxy : F.1.Reachable x y := by
        rw [F.2.2.2]
        exact hPxy.reachable
      exact hFxy.mono le_sup_left
    · have hvbS : S.Reachable v b := by
        apply SimpleGraph.Adj.reachable
        simp only [S, SimpleGraph.sup_adj]
        right
        rw [SimpleGraph.edge_adj]
        exact ⟨Or.inl ⟨rfl, rfl⟩, hvb⟩
      have hbaS : S.Reachable b a := by
        apply SimpleGraph.Reachable.mono le_sup_left
        rw [F.2.2.2]
        exact hab.symm
      rw [SimpleGraph.edge_adj] at hvaxy
      rcases hvaxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hvbS.trans hbaS
      · exact hbaS.symm.trans hvbS.symm
    · exact (show S.Adj x y from Or.inr hvbxy).reachable

/-- A separating two-forest becomes a spanning forest after both new edges
are attached. -/
private noncomputable def spanningForestDoubleExtension
    {V : Type*} [Fintype V] {P : SimpleGraph V} {v a b : V}
    (hva : v ≠ a) (hvb : v ≠ b)
    (hv : P.IsIsolated v) :
    ABTwoForestType P a b → SpanningForestType (seriesExtension P v a b) :=
  fun F ↦ by
    classical
    let S₁ := F.1 ⊔ SimpleGraph.edge v a
    let S := seriesExtension F.1 v a b
    have hFiso : F.1.IsIsolated v := isIsolated_of_le F.2.1 hv
    have hnva : ¬ F.1.Reachable v a :=
      SimpleGraph.not_reachable_of_neighborSet_left_eq_empty hva
        hFiso.neighborSet_eq_empty
    have hnS₁b : ¬ S₁.Reachable v b := by
      intro hreach
      have hfold := reachable_fold_sup_edge hva hFiso hreach
      have habF : F.1.Reachable a b := by
        simpa [S₁, foldVertex, hva, hvb, hvb.symm] using hfold
      exact F.2.2.2.1 habF
    have hSacyclic : S.IsAcyclic := by
      exact (F.2.2.1.sup_edge_of_not_reachable hnva).sup_edge_of_not_reachable
        hnS₁b
    have hSle : S ≤ seriesExtension P v a b := by
      exact sup_le
        (sup_le
          (F.2.1.trans (le_sup_left.trans le_sup_left))
          (le_sup_right.trans le_sup_left))
        le_sup_right
    refine ⟨S, hSle, hSacyclic, ?_⟩
    · apply reachable_eq_of_le_of_adj_reachable hSle
      intro x y hxy
      simp only [seriesExtension, SimpleGraph.sup_adj] at hxy
      rcases hxy with (hPxy | hvaxy) | hvbxy
      · have hFab : (F.1 ⊔ SimpleGraph.edge a b).Reachable x y := by
          rw [F.2.2.2.2]
          exact hPxy.reachable
        exact reachable_replace_edge_by_series hva hvb hFab
      · exact (show S.Adj x y by
          simp only [S, seriesExtension, SimpleGraph.sup_adj]
          exact Or.inl (Or.inr hvaxy)).reachable
      · exact (show S.Adj x y by
          simp only [S, seriesExtension, SimpleGraph.sup_adj]
          exact Or.inr hvbxy).reachable

@[simp] private theorem spanningForestLeftExtension_val
    {V : Type*} [Fintype V] {P : SimpleGraph V} {v a b : V}
    (hva : v ≠ a) (hv : P.IsIsolated v) (hPab : P.Reachable a b)
    (F : SpanningForestType P) :
    (spanningForestLeftExtension hva hv hPab F).1 =
      F.1 ⊔ SimpleGraph.edge v a := rfl

@[simp] private theorem spanningForestRightExtension_val
    {V : Type*} [Fintype V] {P : SimpleGraph V} {v a b : V}
    (hvb : v ≠ b) (hv : P.IsIsolated v) (hPab : P.Reachable a b)
    (F : SpanningForestType P) :
  (spanningForestRightExtension hvb hv hPab F).1 =
      F.1 ⊔ SimpleGraph.edge v b := by
  rfl

@[simp] private theorem spanningForestDoubleExtension_val
    {V : Type*} [Fintype V] {P : SimpleGraph V} {v a b : V}
    (hva : v ≠ a) (hvb : v ≠ b) (hv : P.IsIsolated v)
    (F : ABTwoForestType P a b) :
    (spanningForestDoubleExtension hva hvb hv F).1 =
      seriesExtension F.1 v a b := rfl

@[simp] private theorem spanningForestLeftRestriction_val
    {V : Type*} [Fintype V] {P : SimpleGraph V} {v a b : V}
    (hva : v ≠ a) (hv : P.IsIsolated v)
    (T : SpanningForestType (seriesExtension P v a b))
    (hTa : T.1.Adj v a) (hTb : ¬ T.1.Adj v b) :
    (spanningForestLeftRestriction hva hv T hTa hTb).1 = T.1 ⊓ P := rfl

@[simp] private theorem spanningForestRightRestriction_val
    {V : Type*} [Fintype V] {P : SimpleGraph V} {v a b : V}
    (hvb : v ≠ b) (hv : P.IsIsolated v)
    (T : SpanningForestType (seriesExtension P v a b))
    (hTa : ¬ T.1.Adj v a) (hTb : T.1.Adj v b) :
    (spanningForestRightRestriction hvb hv T hTa hTb).1 = T.1 ⊓ P := rfl

@[simp] private theorem spanningForestDoubleRestriction_val
    {V : Type*} [Fintype V] {P : SimpleGraph V} {v a b : V}
    (hva : v ≠ a) (hvb : v ≠ b) (hab : a ≠ b)
    (hv : P.IsIsolated v) (hPab : P.Reachable a b)
    (T : SpanningForestType (seriesExtension P v a b))
    (hTa : T.1.Adj v a) (hTb : T.1.Adj v b) :
    (spanningForestDoubleRestriction hva hvb hab hv hPab T hTa hTb).1 =
      T.1 ⊓ P := rfl

private theorem restrict_single_extension
    {V : Type*} {F P : SimpleGraph V} {v a : V}
    (hFP : F ≤ P) (hv : P.IsIsolated v) :
    (F ⊔ SimpleGraph.edge v a) ⊓ P = F := by
  ext x y
  constructor
  · intro hxy
    rcases hxy.1 with hFxy | hvaxy
    · exact hFxy
    · exact (hv a (adj_endpoint_of_edge_adj hxy.2 hvaxy)).elim
  · intro hFxy
    exact ⟨Or.inl hFxy, hFP hFxy⟩

private theorem restrict_double_extension
    {V : Type*} {F P : SimpleGraph V} {v a b : V}
    (hFP : F ≤ P) (hv : P.IsIsolated v) :
    seriesExtension F v a b ⊓ P = F := by
  ext x y
  constructor
  · intro hxy
    simp only [seriesExtension] at hxy
    rcases hxy.1 with (hFxy | hvaxy) | hvbxy
    · exact hFxy
    · exact (hv a (adj_endpoint_of_edge_adj hxy.2 hvaxy)).elim
    · exact (hv b (adj_endpoint_of_edge_adj hxy.2 hvbxy)).elim
  · intro hFxy
    exact ⟨Or.inl (Or.inl hFxy), hFP hFxy⟩

private theorem leftExtension_adj_left
    {V : Type*} [Fintype V] {P : SimpleGraph V} {v a b : V}
    (hva : v ≠ a) (hv : P.IsIsolated v) (hPab : P.Reachable a b)
    (F : SpanningForestType P) :
    (spanningForestLeftExtension hva hv hPab F).1.Adj v a := by
  rw [spanningForestLeftExtension_val]
  apply Or.inr
  rw [SimpleGraph.edge_adj]
  exact ⟨Or.inl ⟨rfl, rfl⟩, hva⟩

private theorem leftExtension_not_adj_right
    {V : Type*} [Fintype V] {P : SimpleGraph V} {v a b : V}
    (hva : v ≠ a) (hab : a ≠ b)
    (hv : P.IsIsolated v) (hPab : P.Reachable a b)
    (F : SpanningForestType P) :
    ¬ (spanningForestLeftExtension hva hv hPab F).1.Adj v b := by
  rw [spanningForestLeftExtension_val]
  intro hvbAdj
  rcases hvbAdj with hFvb | hvab
  · exact hv b (F.2.1 hFvb)
  · rcases (SimpleGraph.edge_adj v a v b).mp hvab with
      ⟨⟨_, hba⟩ | ⟨hav, _⟩, _⟩
    · exact hab hba.symm
    · exact hva hav

private theorem rightExtension_not_adj_left
    {V : Type*} [Fintype V] {P : SimpleGraph V} {v a b : V}
    (hvb : v ≠ b) (hab : a ≠ b)
    (hv : P.IsIsolated v) (hPab : P.Reachable a b)
    (F : SpanningForestType P) :
    ¬ (spanningForestRightExtension hvb hv hPab F).1.Adj v a := by
  rw [spanningForestRightExtension_val]
  intro hvaAdj
  rcases hvaAdj with hFva | hvba
  · exact hv a (F.2.1 hFva)
  · rcases (SimpleGraph.edge_adj v b v a).mp hvba with
      ⟨⟨_, hab'⟩ | ⟨hvb', _⟩, _⟩
    · exact hab hab'
    · exact hvb hvb'

private theorem rightExtension_adj_right
    {V : Type*} [Fintype V] {P : SimpleGraph V} {v a b : V}
    (hvb : v ≠ b) (hv : P.IsIsolated v) (hPab : P.Reachable a b)
    (F : SpanningForestType P) :
    (spanningForestRightExtension hvb hv hPab F).1.Adj v b := by
  rw [spanningForestRightExtension_val]
  apply Or.inr
  rw [SimpleGraph.edge_adj]
  exact ⟨Or.inl ⟨rfl, rfl⟩, hvb⟩

private theorem doubleExtension_adj_left
    {V : Type*} [Fintype V] {P : SimpleGraph V} {v a b : V}
    (hva : v ≠ a) (hvb : v ≠ b) (hv : P.IsIsolated v)
    (F : ABTwoForestType P a b) :
    (spanningForestDoubleExtension hva hvb hv F).1.Adj v a := by
  rw [spanningForestDoubleExtension_val]
  simp only [seriesExtension, SimpleGraph.sup_adj]
  left
  right
  rw [SimpleGraph.edge_adj]
  exact ⟨Or.inl ⟨rfl, rfl⟩, hva⟩

private theorem doubleExtension_adj_right
    {V : Type*} [Fintype V] {P : SimpleGraph V} {v a b : V}
    (hva : v ≠ a) (hvb : v ≠ b) (hv : P.IsIsolated v)
    (F : ABTwoForestType P a b) :
    (spanningForestDoubleExtension hva hvb hv F).1.Adj v b := by
  rw [spanningForestDoubleExtension_val]
  simp only [seriesExtension, SimpleGraph.sup_adj]
  right
  rw [SimpleGraph.edge_adj]
  exact ⟨Or.inl ⟨rfl, rfl⟩, hvb⟩

/-! ## The finite series-extension equivalence -/

private abbrev SeriesForestChoice {V : Type*} (P : SimpleGraph V)
    (a b : V) :=
  SpanningForestType P ⊕ (SpanningForestType P ⊕ ABTwoForestType P a b)

private noncomputable def seriesForestEncode
    {V : Type*} [Fintype V] {P : SimpleGraph V} {v a b : V}
    (hva : v ≠ a) (hvb : v ≠ b) (hv : P.IsIsolated v)
    (hPab : P.Reachable a b) :
    SeriesForestChoice P a b →
      SpanningForestType (seriesExtension P v a b)
  | Sum.inl F => spanningForestLeftExtension hva hv hPab F
  | Sum.inr (Sum.inl F) => spanningForestRightExtension hvb hv hPab F
  | Sum.inr (Sum.inr F) => spanningForestDoubleExtension hva hvb hv F

private noncomputable def seriesForestDecode
    {V : Type*} [Fintype V] {P : SimpleGraph V} {v a b : V}
    (hva : v ≠ a) (hvb : v ≠ b) (hab : a ≠ b)
    (hv : P.IsIsolated v) (hPab : P.Reachable a b) :
    SpanningForestType (seriesExtension P v a b) →
      SeriesForestChoice P a b := fun T ↦ by
  classical
  by_cases hTa : T.1.Adj v a
  · by_cases hTb : T.1.Adj v b
    · exact Sum.inr (Sum.inr
        (spanningForestDoubleRestriction hva hvb hab hv hPab T hTa hTb))
    · exact Sum.inl (spanningForestLeftRestriction hva hv T hTa hTb)
  · have hTb : T.1.Adj v b :=
      (spanningForest_has_incident_edge hva hv T).resolve_left hTa
    exact Sum.inr (Sum.inl
      (spanningForestRightRestriction hvb hv T hTa hTb))

private theorem seriesForestDecode_encode
    {V : Type*} [Fintype V] {P : SimpleGraph V} {v a b : V}
    (hva : v ≠ a) (hvb : v ≠ b) (hab : a ≠ b)
    (hv : P.IsIsolated v) (hPab : P.Reachable a b) :
    Function.LeftInverse
      (seriesForestDecode hva hvb hab hv hPab)
      (seriesForestEncode hva hvb hv hPab) := by
  intro choice
  rcases choice with F | F
  · have hTa := leftExtension_adj_left hva hv hPab F
    have hTb := leftExtension_not_adj_right hva hab hv hPab F
    simp only [seriesForestEncode, seriesForestDecode, hTa, hTb,
      dite_true, dite_false]
    apply congrArg Sum.inl
    apply Subtype.ext
    rw [spanningForestLeftRestriction_val,
      spanningForestLeftExtension_val,
      restrict_single_extension F.2.1 hv]
  · rcases F with F | F
    · have hTa := rightExtension_not_adj_left hvb hab hv hPab F
      have hTb := rightExtension_adj_right hvb hv hPab F
      simp only [seriesForestEncode, seriesForestDecode, hTa, hTb,
        dite_true, dite_false]
      apply congrArg (Sum.inr ∘ Sum.inl)
      apply Subtype.ext
      rw [spanningForestRightRestriction_val,
        spanningForestRightExtension_val,
        restrict_single_extension F.2.1 hv]
    · have hTa := doubleExtension_adj_left hva hvb hv F
      have hTb := doubleExtension_adj_right hva hvb hv F
      simp only [seriesForestEncode, seriesForestDecode, hTa, hTb,
        dite_true]
      apply congrArg (Sum.inr ∘ Sum.inr)
      apply Subtype.ext
      rw [spanningForestDoubleRestriction_val,
        spanningForestDoubleExtension_val,
        restrict_double_extension F.2.1 hv]

private theorem seriesForestEncode_decode
    {V : Type*} [Fintype V] {P : SimpleGraph V} {v a b : V}
    (hva : v ≠ a) (hvb : v ≠ b) (hab : a ≠ b)
    (hv : P.IsIsolated v) (hPab : P.Reachable a b) :
    Function.RightInverse
      (seriesForestDecode hva hvb hab hv hPab)
      (seriesForestEncode hva hvb hv hPab) := by
  intro T
  classical
  by_cases hTa : T.1.Adj v a
  · by_cases hTb : T.1.Adj v b
    · simp only [seriesForestDecode, seriesForestEncode, hTa, hTb,
        dite_true]
      apply Subtype.ext
      rw [spanningForestDoubleExtension_val,
        spanningForestDoubleRestriction_val]
      exact (spanningForest_reconstruct_both T hTa hTb).symm
    · simp only [seriesForestDecode, seriesForestEncode, hTa, hTb,
        dite_true, dite_false]
      apply Subtype.ext
      rw [spanningForestLeftExtension_val,
        spanningForestLeftRestriction_val]
      exact (spanningForest_reconstruct_left T hTa hTb).symm
  · have hTb : T.1.Adj v b :=
      (spanningForest_has_incident_edge hva hv T).resolve_left hTa
    simp only [seriesForestDecode, seriesForestEncode, hTa, hTb,
      dite_true, dite_false]
    apply Subtype.ext
    rw [spanningForestRightExtension_val,
      spanningForestRightRestriction_val]
    exact (spanningForest_reconstruct_right T hTa hTb).symm

/-- The three possible states at the new vertex: only the first edge, only
the second edge, or both edges together with a separating two-forest. -/
noncomputable def seriesForestEquiv
    {V : Type*} [Fintype V] {P : SimpleGraph V} {v a b : V}
    (hva : v ≠ a) (hvb : v ≠ b) (hab : a ≠ b)
    (hv : P.IsIsolated v) (hPab : P.Reachable a b) :
    SeriesForestChoice P a b ≃
      SpanningForestType (seriesExtension P v a b) where
  toFun := seriesForestEncode hva hvb hv hPab
  invFun := seriesForestDecode hva hvb hab hv hPab
  left_inv := seriesForestDecode_encode hva hvb hab hv hPab
  right_inv := seriesForestEncode_decode hva hvb hab hv hPab

/-- Exact finite count behind the series-extension rule. -/
theorem spanningForestCount_seriesExtension
    {V : Type*} [Fintype V] {P : SimpleGraph V} {v a b : V}
    (hva : v ≠ a) (hvb : v ≠ b) (hab : a ≠ b)
    (hv : P.IsIsolated v) (hPab : P.Reachable a b) :
    spanningForestCount (seriesExtension P v a b) =
      2 * spanningForestCount P + abTwoForestCount P a b := by
  rw [spanningForestCount, spanningForestCount, abTwoForestCount,
    ← Nat.card_congr (seriesForestEquiv hva hvb hab hv hPab)]
  simp only [Nat.card_sum]
  omega

/-- The conventional effective-resistance series-extension identity. -/
theorem seriesExtension_multiplier_eq_two_add_resistance
    {V : Type*} [Fintype V] {P : SimpleGraph V} {v a b : V}
    (hva : v ≠ a) (hvb : v ≠ b) (hab : a ≠ b)
    (hv : P.IsIsolated v) (hPab : P.Reachable a b) :
    (spanningForestCount (seriesExtension P v a b) : ℝ) /
        spanningForestCount P =
      2 + twoForestResistance P a b := by
  rw [spanningForestCount_seriesExtension hva hvb hab hv hPab]
  have hne : (spanningForestCount P : ℝ) ≠ 0 := by
    exact_mod_cast (spanningForestCount_pos P).ne'
  simp only [twoForestResistance, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  field_simp

/-! ## The words-on-a-page square step -/

/-- Canonical southwest/west neighbour of the new southeast vertex. -/
noncomputable def unitSquareSWVertex
    {V : Type*} {G : SimpleGraph V}
    {coord : V ↪ Boundary.LatticePoint} {z : Boundary.LatticePoint}
    (h : ContainsUnitSquare G coord z) : V :=
  Classical.choose (ContainsUnitSquare.exists_vertex_of_corner
    (w := z) h ⟨by omega, by omega, by omega, by omega⟩)

theorem unitSquareSWVertex_coord
    {V : Type*} {G : SimpleGraph V}
    {coord : V ↪ Boundary.LatticePoint} {z : Boundary.LatticePoint}
    (h : ContainsUnitSquare G coord z) :
    coord (unitSquareSWVertex h) = z :=
  Classical.choose_spec (ContainsUnitSquare.exists_vertex_of_corner
    (w := z) h ⟨by omega, by omega, by omega, by omega⟩)

/-- Canonical northeast/north neighbour of the new southeast vertex. -/
noncomputable def unitSquareNECornerVertex
    {V : Type*} {G : SimpleGraph V}
    {coord : V ↪ Boundary.LatticePoint} {z : Boundary.LatticePoint}
    (h : ContainsUnitSquare G coord z) : V :=
  Classical.choose (ContainsUnitSquare.exists_vertex_of_corner
    (w := (z.1 + 1, z.2 + 1)) h
      ⟨by omega, by omega, by omega, by omega⟩)

theorem unitSquareNECornerVertex_coord
    {V : Type*} {G : SimpleGraph V}
    {coord : V ↪ Boundary.LatticePoint} {z : Boundary.LatticePoint}
    (h : ContainsUnitSquare G coord z) :
    coord (unitSquareNECornerVertex h) = (z.1 + 1, z.2 + 1) :=
  Classical.choose_spec (ContainsUnitSquare.exists_vertex_of_corner
    (w := (z.1 + 1, z.2 + 1)) h
      ⟨by omega, by omega, by omega, by omega⟩)

/-- Canonical northwest vertex giving the old-prefix path from southwest to
northeast. -/
noncomputable def unitSquareNWCornerVertex
    {V : Type*} {G : SimpleGraph V}
    {coord : V ↪ Boundary.LatticePoint} {z : Boundary.LatticePoint}
    (h : ContainsUnitSquare G coord z) : V :=
  Classical.choose (ContainsUnitSquare.exists_vertex_of_corner
    (w := (z.1, z.2 + 1)) h
      ⟨by omega, by omega, by omega, by omega⟩)

theorem unitSquareNWCornerVertex_coord
    {V : Type*} {G : SimpleGraph V}
    {coord : V ↪ Boundary.LatticePoint} {z : Boundary.LatticePoint}
    (h : ContainsUnitSquare G coord z) :
    coord (unitSquareNWCornerVertex h) = (z.1, z.2 + 1) :=
  Classical.choose_spec (ContainsUnitSquare.exists_vertex_of_corner
    (w := (z.1, z.2 + 1)) h
      ⟨by omega, by omega, by omega, by omega⟩)

theorem unitSquareSW_SE_adj
    {V : Type*} {G : SimpleGraph V}
    {coord : V ↪ Boundary.LatticePoint} {z : Boundary.LatticePoint}
    (h : ContainsUnitSquare G coord z) :
    G.Adj (unitSquareSWVertex h) (unitSquareSEVertex h) := by
  rcases h with ⟨sw, se, nw, ne, hsw, hse, hnw, hne,
    hswse, hswnw, hsene, hnwne⟩
  have hsw' : unitSquareSWVertex
      ⟨sw, se, nw, ne, hsw, hse, hnw, hne,
        hswse, hswnw, hsene, hnwne⟩ = sw := by
    apply coord.injective
    rw [unitSquareSWVertex_coord, hsw]
  have hse' : unitSquareSEVertex
      ⟨sw, se, nw, ne, hsw, hse, hnw, hne,
        hswse, hswnw, hsene, hnwne⟩ = se := by
    apply coord.injective
    rw [unitSquareSEVertex_coord, hse]
  simpa only [hsw', hse'] using hswse

theorem unitSquareSE_NE_adj
    {V : Type*} {G : SimpleGraph V}
    {coord : V ↪ Boundary.LatticePoint} {z : Boundary.LatticePoint}
    (h : ContainsUnitSquare G coord z) :
    G.Adj (unitSquareSEVertex h) (unitSquareNECornerVertex h) := by
  rcases h with ⟨sw, se, nw, ne, hsw, hse, hnw, hne,
    hswse, hswnw, hsene, hnwne⟩
  have hse' : unitSquareSEVertex
      ⟨sw, se, nw, ne, hsw, hse, hnw, hne,
        hswse, hswnw, hsene, hnwne⟩ = se := by
    apply coord.injective
    rw [unitSquareSEVertex_coord, hse]
  have hne' : unitSquareNECornerVertex
      ⟨sw, se, nw, ne, hsw, hse, hnw, hne,
        hswse, hswnw, hsene, hnwne⟩ = ne := by
    apply coord.injective
    rw [unitSquareNECornerVertex_coord, hne]
  simpa only [hse', hne'] using hsene

theorem unitSquareSW_NW_adj
    {V : Type*} {G : SimpleGraph V}
    {coord : V ↪ Boundary.LatticePoint} {z : Boundary.LatticePoint}
    (h : ContainsUnitSquare G coord z) :
    G.Adj (unitSquareSWVertex h) (unitSquareNWCornerVertex h) := by
  rcases h with ⟨sw, se, nw, ne, hsw, hse, hnw, hne,
    hswse, hswnw, hsene, hnwne⟩
  have hsw' : unitSquareSWVertex
      ⟨sw, se, nw, ne, hsw, hse, hnw, hne,
        hswse, hswnw, hsene, hnwne⟩ = sw := by
    apply coord.injective
    rw [unitSquareSWVertex_coord, hsw]
  have hnw' : unitSquareNWCornerVertex
      ⟨sw, se, nw, ne, hsw, hse, hnw, hne,
        hswse, hswnw, hsene, hnwne⟩ = nw := by
    apply coord.injective
    rw [unitSquareNWCornerVertex_coord, hnw]
  simpa only [hsw', hnw'] using hswnw

theorem unitSquareNW_NE_adj
    {V : Type*} {G : SimpleGraph V}
    {coord : V ↪ Boundary.LatticePoint} {z : Boundary.LatticePoint}
    (h : ContainsUnitSquare G coord z) :
    G.Adj (unitSquareNWCornerVertex h) (unitSquareNECornerVertex h) := by
  rcases h with ⟨sw, se, nw, ne, hsw, hse, hnw, hne,
    hswse, hswnw, hsene, hnwne⟩
  have hnw' : unitSquareNWCornerVertex
      ⟨sw, se, nw, ne, hsw, hse, hnw, hne,
        hswse, hswnw, hsene, hnwne⟩ = nw := by
    apply coord.injective
    rw [unitSquareNWCornerVertex_coord, hnw]
  have hne' : unitSquareNECornerVertex
      ⟨sw, se, nw, ne, hsw, hse, hnw, hne,
        hswse, hswnw, hsene, hnwne⟩ = ne := by
    apply coord.injective
    rw [unitSquareNECornerVertex_coord, hne]
  simpa only [hnw', hne'] using hnwne

theorem mem_wordsPrefixVertices_of_key_lt
    {V : Type*} [Fintype V] (coord : V ↪ Boundary.LatticePoint)
    (k : ℕ) (hk : k < Fintype.card V) (w : V)
    (hkey : wordsOnPageKey (coord w) <
      wordsOnPageKey (coord
        ((wordsOnPageOrderIso coord).toEquiv ⟨k, hk⟩))) :
    w ∈ wordsPrefixVertices coord k := by
  classical
  letI : LinearOrder V := wordsOnPageLinearOrder coord
  let e := wordsOnPageOrderIso coord
  have hword : @LT.lt V (wordsOnPageLinearOrder coord).toLT w
      (e.toEquiv ⟨k, hk⟩) := by
    exact hkey
  have hfin : e.symm w < e.symm (e.toEquiv ⟨k, hk⟩) :=
    e.symm.lt_iff_lt.mpr hword
  have heq : e.symm (e.toEquiv ⟨k, hk⟩) = ⟨k, hk⟩ :=
    e.symm_apply_apply ⟨k, hk⟩
  rw [heq] at hfin
  rw [wordsPrefixVertices]
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hfin⟩

theorem key_lt_of_mem_wordsPrefixVertices
    {V : Type*} [Fintype V] (coord : V ↪ Boundary.LatticePoint)
    (k : ℕ) (hk : k < Fintype.card V) (w : V)
    (hw : w ∈ wordsPrefixVertices coord k) :
    wordsOnPageKey (coord w) <
      wordsOnPageKey (coord
        ((wordsOnPageOrderIso coord).toEquiv ⟨k, hk⟩)) := by
  classical
  let e := (wordsOnPageOrderIso coord).toEquiv
  have hw' : (e.symm w).1 < k := by
    rw [wordsPrefixVertices] at hw
    exact (Finset.mem_filter.mp hw).2
  have hfin : e.symm w < (⟨k, hk⟩ : Fin (Fintype.card V)) := by
    exact hw'
  have hword : @LT.lt V (wordsOnPageLinearOrder coord).toLT
      (e (e.symm w)) (e ⟨k, hk⟩) :=
    (@OrderIso.lt_iff_lt (Fin (Fintype.card V)) V inferInstance
      (wordsOnPageLinearOrder coord).toPreorder
      (wordsOnPageOrderIso coord) _ _).mpr hfin
  rw [e.apply_symm_apply] at hword
  change wordsOnPageKey (coord w) <
    wordsOnPageKey (coord (e ⟨k, hk⟩)) at hword
  exact hword

private theorem wordsPrefixVertices_succ
    {V : Type*} [Fintype V] [DecidableEq V]
    (coord : V ↪ Boundary.LatticePoint)
    (k : ℕ) (hk : k < Fintype.card V) :
    wordsPrefixVertices coord (k + 1) =
      insert ((wordsOnPageOrderIso coord).toEquiv ⟨k, hk⟩)
        (wordsPrefixVertices coord k) := by
  classical
  ext w
  simp only [wordsPrefixVertices, Finset.mem_filter, Finset.mem_univ,
    true_and, Finset.mem_insert]
  constructor
  · intro hw
    by_cases hwk :
        ((wordsOnPageOrderIso coord).toEquiv.symm w).1 < k
    · exact Or.inr hwk
    · left
      have hval : ((wordsOnPageOrderIso coord).toEquiv.symm w).1 = k := by
        omega
      have hfin : (wordsOnPageOrderIso coord).toEquiv.symm w = ⟨k, hk⟩ :=
        Fin.ext hval
      calc
        w = (wordsOnPageOrderIso coord).toEquiv
            ((wordsOnPageOrderIso coord).toEquiv.symm w) :=
          ((wordsOnPageOrderIso coord).toEquiv.apply_symm_apply w).symm
        _ = (wordsOnPageOrderIso coord).toEquiv ⟨k, hk⟩ :=
          congrArg (wordsOnPageOrderIso coord).toEquiv hfin
  · rintro (rfl | hw)
    · rw [(wordsOnPageOrderIso coord).toEquiv.symm_apply_apply]
      change k < k + 1
      omega
    · omega

private theorem unitSquareSW_mem_wordsPrefix
    {V : Type*} [Fintype V] {G : SimpleGraph V}
    (coord : V ↪ Boundary.LatticePoint) (k : ℕ)
    (hk : k < Fintype.card V) (z : Boundary.LatticePoint)
    (hsquare : ContainsUnitSquare G coord z)
    (hcoord : coord ((wordsOnPageOrderIso coord).toEquiv ⟨k, hk⟩) =
      (z.1 + 1, z.2)) :
    unitSquareSWVertex hsquare ∈ wordsPrefixVertices coord k := by
  apply mem_wordsPrefixVertices_of_key_lt coord k hk
  rw [unitSquareSWVertex_coord, hcoord]
  simp only [wordsOnPageKey, Prod.Lex.lt_iff, ofLex_toLex]
  exact Or.inr ⟨trivial, by omega⟩

private theorem unitSquareNE_mem_wordsPrefix
    {V : Type*} [Fintype V] {G : SimpleGraph V}
    (coord : V ↪ Boundary.LatticePoint) (k : ℕ)
    (hk : k < Fintype.card V) (z : Boundary.LatticePoint)
    (hsquare : ContainsUnitSquare G coord z)
    (hcoord : coord ((wordsOnPageOrderIso coord).toEquiv ⟨k, hk⟩) =
      (z.1 + 1, z.2)) :
    unitSquareNECornerVertex hsquare ∈ wordsPrefixVertices coord k := by
  apply mem_wordsPrefixVertices_of_key_lt coord k hk
  rw [unitSquareNECornerVertex_coord, hcoord]
  simp only [wordsOnPageKey, Prod.Lex.lt_iff, ofLex_toLex]
  exact Or.inl (by omega)

private theorem unitSquareNW_mem_wordsPrefix
    {V : Type*} [Fintype V] {G : SimpleGraph V}
    (coord : V ↪ Boundary.LatticePoint) (k : ℕ)
    (hk : k < Fintype.card V) (z : Boundary.LatticePoint)
    (hsquare : ContainsUnitSquare G coord z)
    (hcoord : coord ((wordsOnPageOrderIso coord).toEquiv ⟨k, hk⟩) =
      (z.1 + 1, z.2)) :
    unitSquareNWCornerVertex hsquare ∈ wordsPrefixVertices coord k := by
  apply mem_wordsPrefixVertices_of_key_lt coord k hk
  rw [unitSquareNWCornerVertex_coord, hcoord]
  simp only [wordsOnPageKey, Prod.Lex.lt_iff, ofLex_toLex]
  exact Or.inl (by omega)

private theorem earlier_lattice_neighbor_of_southeast
    (z w : Boundary.LatticePoint)
    (hadj : Boundary.faceLattice.Adj (z.1 + 1, z.2) w)
    (hkey : wordsOnPageKey w < wordsOnPageKey (z.1 + 1, z.2)) :
    w = z ∨ w = (z.1 + 1, z.2 + 1) := by
  rcases w with ⟨wx, wy⟩
  have hstep := (Boundary.faceLattice_adj_iff_step
    (z.1 + 1, z.2) (wx, wy)).mp hadj
  simp only [Boundary.latticePointToPoint,
    ClosedWalk.Step.vector_east, ClosedWalk.Step.vector_west,
    ClosedWalk.Step.vector_north, ClosedWalk.Step.vector_south,
    Prod.mk_sub_mk, Prod.mk.injEq] at hstep
  norm_num [Nat.cast_add] at hstep
  simp only [wordsOnPageKey, Prod.Lex.lt_iff, ofLex_toLex] at hkey
  rcases hstep with hstep | hstep | hstep | hstep
  · right
    apply Prod.ext <;> omega
  · left
    apply Prod.ext <;> omega
  · right
    apply Prod.ext <;> omega
  · left
    apply Prod.ext <;> omega

/-- At a complete-square southeast step, the new prefix is exactly the old
prefix plus the two incident north/west edges. -/
theorem wordsPrefixGraph_succ_eq_seriesExtension
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    (coord : V ↪ Boundary.LatticePoint) (k : ℕ)
    (hk : k < Fintype.card V) (z : Boundary.LatticePoint)
    (hLattice : G ≤ Boundary.faceLattice.comap coord)
    (hsquare : ContainsUnitSquare G coord z)
    (hcoord : coord ((wordsOnPageOrderIso coord).toEquiv ⟨k, hk⟩) =
      (z.1 + 1, z.2)) :
    wordsPrefixGraph G coord (k + 1) =
      seriesExtension (wordsPrefixGraph G coord k)
        ((wordsOnPageOrderIso coord).toEquiv ⟨k, hk⟩)
        (unitSquareSWVertex hsquare)
        (unitSquareNECornerVertex hsquare) := by
  classical
  let v := (wordsOnPageOrderIso coord).toEquiv ⟨k, hk⟩
  let sw := unitSquareSWVertex hsquare
  let ne := unitSquareNECornerVertex hsquare
  have hsucc := wordsPrefixVertices_succ coord k hk
  have hswOld : sw ∈ wordsPrefixVertices coord k :=
    unitSquareSW_mem_wordsPrefix coord k hk z hsquare hcoord
  have hneOld : ne ∈ wordsPrefixVertices coord k :=
    unitSquareNE_mem_wordsPrefix coord k hk z hsquare hcoord
  have hvse : v = unitSquareSEVertex hsquare := by
    apply coord.injective
    rw [unitSquareSEVertex_coord]
    exact hcoord
  have hGvsw : G.Adj v sw := by
    rw [hvse]
    exact (unitSquareSW_SE_adj hsquare).symm
  have hGvne : G.Adj v ne := by
    rw [hvse]
    exact unitSquareSE_NE_adj hsquare
  ext x y
  change (G.Adj x y ∧ x ∈ wordsPrefixVertices coord (k + 1) ∧
      y ∈ wordsPrefixVertices coord (k + 1)) ↔
    ((G.Adj x y ∧ x ∈ wordsPrefixVertices coord k ∧
        y ∈ wordsPrefixVertices coord k) ∨
      (SimpleGraph.edge v sw).Adj x y) ∨
      (SimpleGraph.edge v ne).Adj x y
  constructor
  · rintro ⟨hGxy, hx, hy⟩
    rw [hsucc] at hx hy
    simp only [Finset.mem_insert] at hx hy
    rcases hx with rfl | hxOld <;> rcases hy with rfl | hyOld
    · exact (G.loopless.irrefl _ hGxy).elim
    · have hlat : Boundary.faceLattice.Adj (z.1 + 1, z.2) (coord y) := by
        rw [← hcoord]
        exact hLattice hGxy
      have hkey := key_lt_of_mem_wordsPrefixVertices coord k hk y hyOld
      rw [hcoord] at hkey
      rcases earlier_lattice_neighbor_of_southeast z (coord y) hlat hkey with
        hySW | hyNE
      · have hyEq : y = sw := by
          apply coord.injective
          exact hySW.trans (unitSquareSWVertex_coord hsquare).symm
        subst y
        left
        right
        rw [SimpleGraph.edge_adj]
        exact ⟨Or.inl ⟨rfl, rfl⟩, hGvsw.ne⟩
      · have hyEq : y = ne := by
          apply coord.injective
          exact hyNE.trans (unitSquareNECornerVertex_coord hsquare).symm
        subst y
        right
        rw [SimpleGraph.edge_adj]
        exact ⟨Or.inl ⟨rfl, rfl⟩, hGvne.ne⟩
    · have hlat : Boundary.faceLattice.Adj (z.1 + 1, z.2) (coord x) := by
        rw [← hcoord]
        exact hLattice hGxy.symm
      have hkey := key_lt_of_mem_wordsPrefixVertices coord k hk x hxOld
      rw [hcoord] at hkey
      rcases earlier_lattice_neighbor_of_southeast z (coord x) hlat hkey with
        hxSW | hxNE
      · have hxEq : x = sw := by
          apply coord.injective
          exact hxSW.trans (unitSquareSWVertex_coord hsquare).symm
        subst x
        left
        right
        rw [SimpleGraph.edge_adj]
        exact ⟨Or.inr ⟨rfl, rfl⟩, hGvsw.ne.symm⟩
      · have hxEq : x = ne := by
          apply coord.injective
          exact hxNE.trans (unitSquareNECornerVertex_coord hsquare).symm
        subst x
        right
        rw [SimpleGraph.edge_adj]
        exact ⟨Or.inr ⟨rfl, rfl⟩, hGvne.ne.symm⟩
    · exact Or.inl (Or.inl ⟨hGxy, hxOld, hyOld⟩)
  · intro hxy
    rcases hxy with (hOld | hswEdge) | hneEdge
    · exact ⟨hOld.1,
        hsucc.symm ▸ Finset.mem_insert_of_mem hOld.2.1,
        hsucc.symm ▸ Finset.mem_insert_of_mem hOld.2.2⟩
    · rcases (SimpleGraph.edge_adj v sw x y).mp hswEdge with
        ⟨⟨rfl, rfl⟩ | ⟨rfl, rfl⟩, _⟩
      · exact ⟨hGvsw,
          hsucc.symm ▸ Finset.mem_insert_self _ _,
          hsucc.symm ▸ Finset.mem_insert_of_mem hswOld⟩
      · exact ⟨hGvsw.symm,
          hsucc.symm ▸ Finset.mem_insert_of_mem hswOld,
          hsucc.symm ▸ Finset.mem_insert_self _ _⟩
    · rcases (SimpleGraph.edge_adj v ne x y).mp hneEdge with
        ⟨⟨rfl, rfl⟩ | ⟨rfl, rfl⟩, _⟩
      · exact ⟨hGvne,
          hsucc.symm ▸ Finset.mem_insert_self _ _,
          hsucc.symm ▸ Finset.mem_insert_of_mem hneOld⟩
      · exact ⟨hGvne.symm,
          hsucc.symm ▸ Finset.mem_insert_of_mem hneOld,
          hsucc.symm ▸ Finset.mem_insert_self _ _⟩

theorem wordsPrefixGraph_current_isIsolated
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    (coord : V ↪ Boundary.LatticePoint) (k : ℕ)
    (hk : k < Fintype.card V) :
    (wordsPrefixGraph G coord k).IsIsolated
      ((wordsOnPageOrderIso coord).toEquiv ⟨k, hk⟩) := by
  classical
  let v := (wordsOnPageOrderIso coord).toEquiv ⟨k, hk⟩
  have hvNot : v ∉ wordsPrefixVertices coord k := by
    rw [wordsPrefixVertices]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    change (((wordsOnPageOrderIso coord).toEquiv.symm
      ((wordsOnPageOrderIso coord).toEquiv ⟨k, hk⟩)).1 < k) → False
    rw [(wordsOnPageOrderIso coord).toEquiv.symm_apply_apply]
    exact Nat.lt_irrefl k
  intro w hvw
  exact hvNot hvw.2.1

theorem wordsPrefixGraph_square_neighbors_reachable
    {V : Type*} [Fintype V] {G : SimpleGraph V}
    (coord : V ↪ Boundary.LatticePoint) (k : ℕ)
    (hk : k < Fintype.card V) (z : Boundary.LatticePoint)
    (hsquare : ContainsUnitSquare G coord z)
    (hcoord : coord ((wordsOnPageOrderIso coord).toEquiv ⟨k, hk⟩) =
      (z.1 + 1, z.2)) :
    (wordsPrefixGraph G coord k).Reachable
      (unitSquareSWVertex hsquare) (unitSquareNECornerVertex hsquare) := by
  classical
  have hsw := unitSquareSW_mem_wordsPrefix coord k hk z hsquare hcoord
  have hnw := unitSquareNW_mem_wordsPrefix coord k hk z hsquare hcoord
  have hne := unitSquareNE_mem_wordsPrefix coord k hk z hsquare hcoord
  have hswNW : (wordsPrefixGraph G coord k).Adj
      (unitSquareSWVertex hsquare) (unitSquareNWCornerVertex hsquare) :=
    ⟨unitSquareSW_NW_adj hsquare, hsw, hnw⟩
  have hnwNE : (wordsPrefixGraph G coord k).Adj
      (unitSquareNWCornerVertex hsquare) (unitSquareNECornerVertex hsquare) :=
    ⟨unitSquareNW_NE_adj hsquare, hnw, hne⟩
  exact hswNW.reachable.trans hnwNE.reachable

theorem square_step_vertices_pairwise_ne
    {V : Type*} [Fintype V] {G : SimpleGraph V}
    (coord : V ↪ Boundary.LatticePoint) (k : ℕ)
    (hk : k < Fintype.card V) (z : Boundary.LatticePoint)
    (hsquare : ContainsUnitSquare G coord z)
    (hcoord : coord ((wordsOnPageOrderIso coord).toEquiv ⟨k, hk⟩) =
      (z.1 + 1, z.2)) :
    ((wordsOnPageOrderIso coord).toEquiv ⟨k, hk⟩ ≠
        unitSquareSWVertex hsquare) ∧
      ((wordsOnPageOrderIso coord).toEquiv ⟨k, hk⟩ ≠
        unitSquareNECornerVertex hsquare) ∧
      unitSquareSWVertex hsquare ≠ unitSquareNECornerVertex hsquare := by
  constructor
  · intro heq
    have hc := congrArg coord heq
    rw [hcoord, unitSquareSWVertex_coord] at hc
    have hx := congrArg Prod.fst hc
    omega
  constructor
  · intro heq
    have hc := congrArg coord heq
    rw [hcoord, unitSquareNECornerVertex_coord] at hc
    have hy := congrArg Prod.snd hc
    omega
  · intro heq
    have hc := congrArg coord heq
    rw [unitSquareSWVertex_coord, unitSquareNECornerVertex_coord] at hc
    have hy := congrArg Prod.snd hc
    omega

/-- The prefix multiplier at a complete southeast square step is exactly
`2 +` the genuine old-prefix two-forest resistance. -/
theorem wordsPrefixMultiplier_eq_two_add_twoForestResistance
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    (coord : V ↪ Boundary.LatticePoint) (k : ℕ)
    (hk : k < Fintype.card V) (z : Boundary.LatticePoint)
    (hLattice : G ≤ Boundary.faceLattice.comap coord)
    (hsquare : ContainsUnitSquare G coord z)
    (hcoord : coord ((wordsOnPageOrderIso coord).toEquiv ⟨k, hk⟩) =
      (z.1 + 1, z.2)) :
    wordsPrefixMultiplier G coord k =
      2 + twoForestResistance (wordsPrefixGraph G coord k)
        (unitSquareSWVertex hsquare) (unitSquareNECornerVertex hsquare) := by
  rcases square_step_vertices_pairwise_ne coord k hk z hsquare hcoord with
    ⟨hvsw, hvne, hswne⟩
  rw [wordsPrefixMultiplier,
    wordsPrefixGraph_succ_eq_seriesExtension G coord k hk z hLattice hsquare hcoord]
  exact seriesExtension_multiplier_eq_two_add_resistance
    hvsw hvne hswne (wordsPrefixGraph_current_isIsolated G coord k hk)
    (wordsPrefixGraph_square_neighbors_reachable coord k hk z hsquare hcoord)

/-! ## The sole remaining half-plane/Rayleigh input -/

/-- The genuine effective-resistance estimate left by the deterministic
reduction.  Its numerator is the explicitly defined number of separating
two-forests of the old prefix, rather than a renamed prefix multiplier.

Tapp's source proof obtains this inequality by Rayleigh monotonicity against
finite words-on-a-page half-plane exhaustions and then passes to the bulk
tree-entropy limit. -/
def HalfPlaneTwoForestResistanceBound (κ : ℝ) : Prop :=
  ∀ {V : Type} [Fintype V]
    (G : SimpleGraph V) (coord : V ↪ Boundary.LatticePoint)
    (k : ℕ) (hk : k < Fintype.card V) (z : Boundary.LatticePoint),
    ∀ (_hLattice : G ≤ Boundary.faceLattice.comap coord)
      (hsquare : ContainsUnitSquare G coord z)
      (_hcoord : coord ((wordsOnPageOrderIso coord).toEquiv ⟨k, hk⟩) =
        (z.1 + 1, z.2)),
    Real.exp κ - 2 ≤
      twoForestResistance (wordsPrefixGraph G coord k)
        (unitSquareSWVertex hsquare)
        (unitSquareNECornerVertex hsquare)

/-- The two-forest Rayleigh estimate implies the older multiplier-form
interface by the proved finite series-extension identity. -/
theorem HalfPlaneTwoForestResistanceBound.toHalfPlaneResistanceBound
    {κ : ℝ} (h : HalfPlaneTwoForestResistanceBound κ) :
    HalfPlaneResistanceBound κ := by
  intro V _ G coord k hk z hLattice hsquare hcoord
  have htwo := h G coord k hk z hLattice hsquare hcoord
  rw [wordsPrefixResistance,
    wordsPrefixMultiplier_eq_two_add_twoForestResistance
      G coord k hk z hLattice hsquare hcoord]
  linarith

/-- The local two-forest/Rayleigh estimate is sufficient for the full Tapp
square-family lower bound. -/
theorem tappSquareFamilyLowerBound_of_halfPlaneTwoForestResistance
    {κ : ℝ} (h : HalfPlaneTwoForestResistanceBound κ) :
    TappSquareFamilyLowerBound κ :=
  tappSquareFamilyLowerBound_of_halfPlaneResistance
    h.toHalfPlaneResistanceBound
end Dual
end SquareMaximality
