import SquareMaximality.Dual.TappBulk

/-!
# Boundary prefix bounds for the square scan

The words-on-a-page enumeration first exposes the top row from left to
right and then proceeds row by row downwards.  Thus a vertex on the top or
left boundary has at most one neighbour in the preceding prefix.  This file
formalizes the elementary fact that adjoining such an isolated vertex by a
single leaf edge does not change the number of maximal spanning forests.
-/

set_option autoImplicit false

namespace SquareMaximality
namespace Dual

noncomputable section

/-! ## A single-leaf extension -/

/-- Attach the isolated vertex `v` to `a` by one edge. -/
private def leafExtension {V : Type*} (P : SimpleGraph V) (v a : V) :
    SimpleGraph V :=
  P ⊔ SimpleGraph.edge v a

/-- Replace the new leaf by its attachment vertex. -/
private def leafFold {V : Type*} [DecidableEq V] (v a : V) (x : V) : V :=
  if x = v then a else x

private theorem prefix_reachable_eq_of_le_of_adj_reachable
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

private theorem prefix_isIsolated_of_le
    {V : Type*} {F P : SimpleGraph V} {v : V}
    (hFP : F ≤ P) (hv : P.IsIsolated v) : F.IsIsolated v := by
  intro w hvw
  exact hv w (hFP hvw)

private theorem prefix_edge_le_of_adj
    {V : Type*} {G : SimpleGraph V} {x y : V} (hxy : G.Adj x y) :
    SimpleGraph.edge x y ≤ G :=
  (SimpleGraph.edge_le_iff G).mpr (Or.inr hxy)

private theorem prefix_adj_endpoint_of_edge_adj
    {V : Type*} {G : SimpleGraph V} {v a x y : V}
    (hG : G.Adj x y) (hEdge : (SimpleGraph.edge v a).Adj x y) :
    G.Adj v a := by
  rcases (SimpleGraph.edge_adj v a x y).mp hEdge with
    ⟨⟨rfl, rfl⟩ | ⟨rfl, rfl⟩, _⟩
  · exact hG
  · exact hG.symm

/-- Folding the only new edge gives a walk in the old graph. -/
private theorem prefix_reachable_fold_leafExtension
    {V : Type*} [DecidableEq V] {P : SimpleGraph V} {v a x y : V}
    (hva : v ≠ a) (hv : P.IsIsolated v)
    (hxy : (leafExtension P v a).Reachable x y) :
    P.Reachable (leafFold v a x) (leafFold v a y) := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at hxy ⊢
  exact hxy.lift' (leafFold v a) fun p q hpq ↦ by
    rw [leafExtension, SimpleGraph.sup_adj] at hpq
    rcases hpq with hpq | hpq
    · have hpv : p ≠ v := fun hpv ↦ hv q (hpv ▸ hpq)
      have hqv : q ≠ v := fun hqv ↦ hv p (hqv ▸ hpq.symm)
      exact (SimpleGraph.reachable_iff_reflTransGen _ _).mp <| by
        simpa [leafFold, hpv, hqv] using hpq.reachable
    · rw [SimpleGraph.edge_adj] at hpq
      rcases hpq with ⟨hpv, hqa⟩ | ⟨hpa, hqv⟩
      · rw [hpv, hqa]
        simpa [Function.onFun, leafFold, hva, hva.symm] using
          (Relation.ReflTransGen.refl : Relation.ReflTransGen P.Adj a a)
      · rw [hpa, hqv]
        simpa [Function.onFun, leafFold, hva, hva.symm] using
          (Relation.ReflTransGen.refl : Relation.ReflTransGen P.Adj a a)

private theorem prefix_leaf_edge_mem
    {V : Type*} {P : SimpleGraph V} {v a : V}
    (hva : v ≠ a) (hv : P.IsIsolated v)
    (T : SpanningForestType (leafExtension P v a)) :
    T.1.Adj v a := by
  by_contra hnot
  have hTiso : T.1.IsIsolated v := by
    intro x hvx
    have hQvx := T.2.1 hvx
    rcases hQvx with hPvx | hvax
    · exact hv x hPvx
    · exact hnot (prefix_adj_endpoint_of_edge_adj hvx hvax)
  have hQva : (leafExtension P v a).Reachable v a := by
    apply SimpleGraph.Adj.reachable
    apply Or.inr
    rw [SimpleGraph.edge_adj]
    exact ⟨Or.inl ⟨rfl, rfl⟩, hva⟩
  have hTva : T.1.Reachable v a := by
    rw [T.2.2.2]
    exact hQva
  exact (SimpleGraph.not_reachable_of_neighborSet_left_eq_empty hva
    hTiso.neighborSet_eq_empty) hTva

private theorem prefix_leaf_reconstruct
    {V : Type*} {P : SimpleGraph V} {v a : V}
    (T : SpanningForestType (leafExtension P v a))
    (hva : T.1.Adj v a) :
    T.1 = (T.1 ⊓ P) ⊔ SimpleGraph.edge v a := by
  calc
    T.1 = T.1 ⊓ leafExtension P v a :=
      (inf_eq_left.mpr T.2.1).symm
    _ = (T.1 ⊓ P) ⊔ (T.1 ⊓ SimpleGraph.edge v a) := by
      simp only [leafExtension, inf_sup_left]
    _ = (T.1 ⊓ P) ⊔ SimpleGraph.edge v a := by
      rw [inf_eq_right.mpr (prefix_edge_le_of_adj hva)]

/-- Intersecting a leaf extension with the old graph removes exactly the
new leaf edge. -/
private theorem prefix_restrict_leaf_extension
    {V : Type*} {F P : SimpleGraph V} {v a : V}
    (hFP : F ≤ P) (hv : P.IsIsolated v) :
    (F ⊔ SimpleGraph.edge v a) ⊓ P = F := by
  ext x y
  constructor
  · intro hxy
    rcases hxy.1 with hFxy | hvaxy
    · exact hFxy
    · exact (hv a (prefix_adj_endpoint_of_edge_adj hxy.2 hvaxy)).elim
  · intro hFxy
    exact ⟨Or.inl hFxy, hFP hFxy⟩

/-- Add the compulsory leaf edge to a maximal spanning forest. -/
private noncomputable def prefix_leafForestExtension
    {V : Type*} [Fintype V] {P : SimpleGraph V} {v a : V}
    (hva : v ≠ a) (hv : P.IsIsolated v) :
    SpanningForestType P → SpanningForestType (leafExtension P v a) :=
  fun F ↦ by
    let S := F.1 ⊔ SimpleGraph.edge v a
    have hFiso : F.1.IsIsolated v := prefix_isIsolated_of_le F.2.1 hv
    have hnreach : ¬ F.1.Reachable v a :=
      SimpleGraph.not_reachable_of_neighborSet_left_eq_empty hva
        hFiso.neighborSet_eq_empty
    have hSle : S ≤ leafExtension P v a :=
      sup_le (F.2.1.trans le_sup_left) le_sup_right
    refine ⟨S, hSle, F.2.2.1.sup_edge_of_not_reachable hnreach, ?_⟩
    apply prefix_reachable_eq_of_le_of_adj_reachable hSle
    intro x y hxy
    rcases hxy with hPxy | hvaxy
    · have hFxy : F.1.Reachable x y := by
        rw [F.2.2.2]
        exact hPxy.reachable
      exact hFxy.mono le_sup_left
    · exact (show S.Adj x y from Or.inr hvaxy).reachable

/-- Remove the compulsory leaf edge from a maximal spanning forest. -/
private noncomputable def prefix_leafForestRestriction
    {V : Type*} [Fintype V] {P : SimpleGraph V} {v a : V}
    (hva : v ≠ a) (hv : P.IsIsolated v) :
    SpanningForestType (leafExtension P v a) → SpanningForestType P :=
  fun T ↦ by
    classical
    let R := T.1 ⊓ P
    have hRiso : R.IsIsolated v := prefix_isIsolated_of_le inf_le_right hv
    have hleaf : T.1.Adj v a := prefix_leaf_edge_mem hva hv T
    have hreconstruct : T.1 = R ⊔ SimpleGraph.edge v a :=
      prefix_leaf_reconstruct T hleaf
    refine ⟨R, inf_le_right, T.2.2.1.anti inf_le_left, ?_⟩
    apply prefix_reachable_eq_of_le_of_adj_reachable inf_le_right
    intro x y hPxy
    have hxv : x ≠ v := fun hxv ↦ hv y (hxv ▸ hPxy)
    have hyv : y ≠ v := fun hyv ↦ hv x (hyv ▸ hPxy.symm)
    have hTxy : T.1.Reachable x y := by
      rw [T.2.2.2]
      exact (show (leafExtension P v a).Adj x y from Or.inl hPxy).reachable
    rw [hreconstruct] at hTxy
    have hfold := prefix_reachable_fold_leafExtension hva hRiso hTxy
    simpa [R, leafExtension, leafFold, hxv, hyv] using hfold

/-- Spanning forests are unchanged by attaching an isolated vertex as a
leaf. -/
private noncomputable def prefix_leafForestEquiv
    {V : Type*} [Fintype V] {P : SimpleGraph V} {v a : V}
    (hva : v ≠ a) (hv : P.IsIsolated v) :
    SpanningForestType P ≃ SpanningForestType (leafExtension P v a) where
  toFun := prefix_leafForestExtension hva hv
  invFun := prefix_leafForestRestriction hva hv
  left_inv := by
    intro F
    apply Subtype.ext
    exact prefix_restrict_leaf_extension F.2.1 hv
  right_inv := by
    intro T
    apply Subtype.ext
    exact (prefix_leaf_reconstruct T (prefix_leaf_edge_mem hva hv T)).symm

private theorem prefix_spanningForestCount_leafExtension
    {V : Type*} [Fintype V] {P : SimpleGraph V} {v a : V}
    (hva : v ≠ a) (hv : P.IsIsolated v) :
    spanningForestCount (leafExtension P v a) = spanningForestCount P := by
  rw [spanningForestCount, spanningForestCount]
  exact (Nat.card_congr (prefix_leafForestEquiv hva hv)).symm

/-! ## Prefix geometry -/

private theorem prefix_wordsPrefixVertices_succ
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

/-- If the current vertex has exactly one earlier neighbour, the new prefix
is the old prefix with that leaf edge adjoined. -/
private theorem prefix_wordsPrefixGraph_succ_eq_leafExtension
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    (coord : V ↪ Boundary.LatticePoint) (k : ℕ)
    (hk : k < Fintype.card V) (a : V)
    (haOld : a ∈ wordsPrefixVertices coord k)
    (hva : G.Adj
      ((wordsOnPageOrderIso coord).toEquiv ⟨k, hk⟩) a)
    (hunique : ∀ w, w ∈ wordsPrefixVertices coord k →
      G.Adj ((wordsOnPageOrderIso coord).toEquiv ⟨k, hk⟩) w → w = a) :
    wordsPrefixGraph G coord (k + 1) =
      leafExtension (wordsPrefixGraph G coord k)
        ((wordsOnPageOrderIso coord).toEquiv ⟨k, hk⟩) a := by
  classical
  let v := (wordsOnPageOrderIso coord).toEquiv ⟨k, hk⟩
  have hsucc := prefix_wordsPrefixVertices_succ coord k hk
  ext x y
  change (G.Adj x y ∧ x ∈ wordsPrefixVertices coord (k + 1) ∧
      y ∈ wordsPrefixVertices coord (k + 1)) ↔
    (G.Adj x y ∧ x ∈ wordsPrefixVertices coord k ∧
        y ∈ wordsPrefixVertices coord k) ∨
      (SimpleGraph.edge v a).Adj x y
  constructor
  · rintro ⟨hGxy, hx, hy⟩
    rw [hsucc] at hx hy
    simp only [Finset.mem_insert] at hx hy
    rcases hx with rfl | hxOld <;> rcases hy with rfl | hyOld
    · exact (G.loopless.irrefl _ hGxy).elim
    · have hya : y = a := hunique y hyOld hGxy
      subst y
      apply Or.inr
      rw [SimpleGraph.edge_adj]
      exact ⟨Or.inl ⟨rfl, rfl⟩, hva.ne⟩
    · have hxa : x = a := hunique x hxOld hGxy.symm
      subst x
      apply Or.inr
      rw [SimpleGraph.edge_adj]
      exact ⟨Or.inr ⟨rfl, rfl⟩, hva.ne.symm⟩
    · exact Or.inl ⟨hGxy, hxOld, hyOld⟩
  · intro hxy
    rcases hxy with hOld | hEdge
    · exact ⟨hOld.1,
        hsucc.symm ▸ Finset.mem_insert_of_mem hOld.2.1,
        hsucc.symm ▸ Finset.mem_insert_of_mem hOld.2.2⟩
    · rcases (SimpleGraph.edge_adj v a x y).mp hEdge with
        ⟨⟨rfl, rfl⟩ | ⟨rfl, rfl⟩, _⟩
      · exact ⟨hva,
          hsucc.symm ▸ Finset.mem_insert_self _ _,
          hsucc.symm ▸ Finset.mem_insert_of_mem haOld⟩
      · exact ⟨hva.symm,
          hsucc.symm ▸ Finset.mem_insert_of_mem haOld,
          hsucc.symm ▸ Finset.mem_insert_self _ _⟩

/-- If the current vertex has no earlier neighbour, exposing it changes no
edges of the prefix graph. -/
private theorem prefix_wordsPrefixGraph_succ_eq_self
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    (coord : V ↪ Boundary.LatticePoint) (k : ℕ)
    (hk : k < Fintype.card V)
    (hnone : ∀ w, w ∈ wordsPrefixVertices coord k →
      ¬ G.Adj ((wordsOnPageOrderIso coord).toEquiv ⟨k, hk⟩) w) :
    wordsPrefixGraph G coord (k + 1) = wordsPrefixGraph G coord k := by
  classical
  let v := (wordsOnPageOrderIso coord).toEquiv ⟨k, hk⟩
  have hsucc := prefix_wordsPrefixVertices_succ coord k hk
  ext x y
  change (G.Adj x y ∧ x ∈ wordsPrefixVertices coord (k + 1) ∧
      y ∈ wordsPrefixVertices coord (k + 1)) ↔
    G.Adj x y ∧ x ∈ wordsPrefixVertices coord k ∧
      y ∈ wordsPrefixVertices coord k
  constructor
  · rintro ⟨hGxy, hx, hy⟩
    rw [hsucc] at hx hy
    simp only [Finset.mem_insert] at hx hy
    rcases hx with rfl | hxOld <;> rcases hy with rfl | hyOld
    · exact (G.loopless.irrefl _ hGxy).elim
    · exact (hnone y hyOld hGxy).elim
    · exact (hnone x hxOld hGxy.symm).elim
    · exact ⟨hGxy, hxOld, hyOld⟩
  · rintro ⟨hGxy, hx, hy⟩
    exact ⟨hGxy,
      hsucc.symm ▸ Finset.mem_insert_of_mem hx,
      hsucc.symm ▸ Finset.mem_insert_of_mem hy⟩

/-- The earlier lattice neighbours of a vertex are precisely its west and
north neighbours (when those natural-coordinate vertices exist). -/
private theorem prefix_earlier_lattice_neighbor
    (p w : Boundary.LatticePoint)
    (hadj : Boundary.faceLattice.Adj p w)
    (hkey : wordsOnPageKey w < wordsOnPageKey p) :
    w = (p.1 - 1, p.2) ∨ w = (p.1, p.2 + 1) := by
  rcases p with ⟨px, py⟩
  rcases w with ⟨wx, wy⟩
  have hstep := (Boundary.faceLattice_adj_iff_step
    (px, py) (wx, wy)).mp hadj
  simp only [Boundary.latticePointToPoint,
    ClosedWalk.Step.vector_east, ClosedWalk.Step.vector_west,
    ClosedWalk.Step.vector_north, ClosedWalk.Step.vector_south,
    Prod.mk_sub_mk, Prod.mk.injEq] at hstep
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

/-! ## The square boundary multiplier -/

/-- Every left- or top-boundary step in the square enumeration has
multiplier exactly one. -/
theorem squareBoundaryPrefixMultiplierOne :
    SquareBoundaryPrefixMultiplierOne := by
  intro n k hk
  let p : Fin n × Fin n :=
    (wordsOnPageOrderIso (squareGridCoord n)).toEquiv ⟨k, hk⟩
  change p.1.1 = 0 ∨ p.2.1 + 1 = n →
    wordsPrefixMultiplier (squareGrid n) (squareGridCoord n) k = 1
  intro hboundary
  rcases hboundary with hleft | htop
  · by_cases hpy : p.2.1 + 1 < n
    · let a : Fin n × Fin n := squareStepNE p hpy
      have haOld : a ∈ wordsPrefixVertices (squareGridCoord n) k := by
        apply mem_wordsPrefixVertices_of_key_lt (squareGridCoord n) k hk
        change wordsOnPageKey (p.1.1, p.2.1 + 1) <
          wordsOnPageKey (p.1.1, p.2.1)
        simp only [wordsOnPageKey, Prod.Lex.lt_iff, ofLex_toLex]
        exact Or.inl (by omega)
      have hva : (squareGrid n).Adj p a := by
        rw [squareGrid, rectanglePrimal_toSimpleGraph]
        right
        constructor
        · rw [SimpleGraph.pathGraph_adj]
          left
          simp [a, squareStepNE]
        · rfl
      have hunique : ∀ w,
          w ∈ wordsPrefixVertices (squareGridCoord n) k →
          (squareGrid n).Adj p w → w = a := by
        intro w hw hpw
        have hkey := key_lt_of_mem_wordsPrefixVertices
          (squareGridCoord n) k hk w hw
        have hlat : Boundary.faceLattice.Adj
            (squareGridCoord n p) (squareGridCoord n w) :=
          squareGrid_le_faceLattice n hpw
        rcases prefix_earlier_lattice_neighbor
            (squareGridCoord n p) (squareGridCoord n w) hlat hkey with
          hwest | hnorth
        · have hwp : w = p := by
            apply (squareGridCoord n).injective
            simpa [hleft] using hwest
          subst w
          exact (lt_irrefl _ hkey).elim
        · apply (squareGridCoord n).injective
          simpa [a, squareStepNE] using hnorth
      have hgraph := prefix_wordsPrefixGraph_succ_eq_leafExtension
        (squareGrid n) (squareGridCoord n) k hk a haOld hva hunique
      have hiso := wordsPrefixGraph_current_isIsolated
        (squareGrid n) (squareGridCoord n) k hk
      have hpa : p ≠ a := by
        intro hpa
        have heq := congrArg (fun q : Fin n × Fin n ↦ q.2.1) hpa
        simp only [a, squareStepNE] at heq
        omega
      have hcount := prefix_spanningForestCount_leafExtension hpa hiso
      have hpos :
          (spanningForestCount
            (wordsPrefixGraph (squareGrid n) (squareGridCoord n) k) : ℝ) ≠ 0 := by
        exact_mod_cast (spanningForestCount_pos
          (wordsPrefixGraph (squareGrid n) (squareGridCoord n) k)).ne'
      rw [wordsPrefixMultiplier, hgraph, hcount, div_self hpos]
    · have htop' : p.2.1 + 1 = n := by omega
      have hnone : ∀ w,
          w ∈ wordsPrefixVertices (squareGridCoord n) k →
          ¬ (squareGrid n).Adj p w := by
        intro w hw hpw
        have hkey := key_lt_of_mem_wordsPrefixVertices
          (squareGridCoord n) k hk w hw
        have hlat : Boundary.faceLattice.Adj
            (squareGridCoord n p) (squareGridCoord n w) :=
          squareGrid_le_faceLattice n hpw
        rcases prefix_earlier_lattice_neighbor
            (squareGridCoord n p) (squareGridCoord n w) hlat hkey with
          hwest | hnorth
        · have hwp : w = p := by
            apply (squareGridCoord n).injective
            simpa [hleft] using hwest
          subst w
          exact (lt_irrefl _ hkey).elim
        · have heq := congrArg Prod.snd hnorth
          simp only [squareGridCoord_apply] at heq
          omega
      have hgraph := prefix_wordsPrefixGraph_succ_eq_self
        (squareGrid n) (squareGridCoord n) k hk hnone
      have hpos :
          (spanningForestCount
            (wordsPrefixGraph (squareGrid n) (squareGridCoord n) k) : ℝ) ≠ 0 := by
        exact_mod_cast (spanningForestCount_pos
          (wordsPrefixGraph (squareGrid n) (squareGridCoord n) k)).ne'
      rw [wordsPrefixMultiplier, hgraph, div_self hpos]
  · by_cases hpx : 0 < p.1.1
    · let a : Fin n × Fin n := squareStepSW p hpx
      have haOld : a ∈ wordsPrefixVertices (squareGridCoord n) k := by
        apply mem_wordsPrefixVertices_of_key_lt (squareGridCoord n) k hk
        change wordsOnPageKey (p.1.1 - 1, p.2.1) <
          wordsOnPageKey (p.1.1, p.2.1)
        simp only [wordsOnPageKey, Prod.Lex.lt_iff, ofLex_toLex]
        exact Or.inr ⟨trivial, by omega⟩
      have hva : (squareGrid n).Adj p a := by
        rw [squareGrid, rectanglePrimal_toSimpleGraph]
        left
        constructor
        · rw [SimpleGraph.pathGraph_adj]
          right
          simp [a, squareStepSW]
          omega
        · rfl
      have hunique : ∀ w,
          w ∈ wordsPrefixVertices (squareGridCoord n) k →
          (squareGrid n).Adj p w → w = a := by
        intro w hw hpw
        have hkey := key_lt_of_mem_wordsPrefixVertices
          (squareGridCoord n) k hk w hw
        have hlat : Boundary.faceLattice.Adj
            (squareGridCoord n p) (squareGridCoord n w) :=
          squareGrid_le_faceLattice n hpw
        rcases prefix_earlier_lattice_neighbor
            (squareGridCoord n p) (squareGridCoord n w) hlat hkey with
          hwest | hnorth
        · apply (squareGridCoord n).injective
          simpa [a, squareStepSW] using hwest
        · have heq := congrArg Prod.snd hnorth
          simp only [squareGridCoord_apply] at heq
          omega
      have hgraph := prefix_wordsPrefixGraph_succ_eq_leafExtension
        (squareGrid n) (squareGridCoord n) k hk a haOld hva hunique
      have hiso := wordsPrefixGraph_current_isIsolated
        (squareGrid n) (squareGridCoord n) k hk
      have hpa : p ≠ a := by
        intro hpa
        have heq := congrArg (fun q : Fin n × Fin n ↦ q.1.1) hpa
        simp only [a, squareStepSW] at heq
        omega
      have hcount := prefix_spanningForestCount_leafExtension hpa hiso
      have hpos :
          (spanningForestCount
            (wordsPrefixGraph (squareGrid n) (squareGridCoord n) k) : ℝ) ≠ 0 := by
        exact_mod_cast (spanningForestCount_pos
          (wordsPrefixGraph (squareGrid n) (squareGridCoord n) k)).ne'
      rw [wordsPrefixMultiplier, hgraph, hcount, div_self hpos]
    · have hleft : p.1.1 = 0 := Nat.eq_zero_of_not_pos hpx
      have hnone : ∀ w,
          w ∈ wordsPrefixVertices (squareGridCoord n) k →
          ¬ (squareGrid n).Adj p w := by
        intro w hw hpw
        have hkey := key_lt_of_mem_wordsPrefixVertices
          (squareGridCoord n) k hk w hw
        have hlat : Boundary.faceLattice.Adj
            (squareGridCoord n p) (squareGridCoord n w) :=
          squareGrid_le_faceLattice n hpw
        rcases prefix_earlier_lattice_neighbor
            (squareGridCoord n p) (squareGridCoord n w) hlat hkey with
          hwest | hnorth
        · have hwp : w = p := by
            apply (squareGridCoord n).injective
            simpa [hleft] using hwest
          subst w
          exact (lt_irrefl _ hkey).elim
        · have heq := congrArg Prod.snd hnorth
          simp only [squareGridCoord_apply] at heq
          omega
      have hgraph := prefix_wordsPrefixGraph_succ_eq_self
        (squareGrid n) (squareGridCoord n) k hk hnone
      have hpos :
          (spanningForestCount
            (wordsPrefixGraph (squareGrid n) (squareGridCoord n) k) : ℝ) ≠ 0 := by
        exact_mod_cast (spanningForestCount_pos
          (wordsPrefixGraph (squareGrid n) (squareGridCoord n) k)).ne'
      rw [wordsPrefixMultiplier, hgraph, div_self hpos]

/-- With the boundary steps discharged, the only local ingredient in the
uniform factor-four estimate is the complete-square resistance bound. -/
theorem squarePrefixMultiplierUpperBound_four_of_complete
    (hcomplete : SquareCompleteStepResistanceUpperBound) :
    SquarePrefixMultiplierUpperBound 4 :=
  squarePrefixMultiplierUpperBound_four_of_local
    squareBoundaryPrefixMultiplierOne hcomplete

end

end Dual
end SquareMaximality
