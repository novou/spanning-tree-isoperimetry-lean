module

public import SquareMaximality.Dual.Encoding
public import SquareMaximality.Boundary.Canonical
public import SquareMaximality.Multigraph.Events

@[expose] public section

set_option backward.privateInPublic true

/-!
# Dual edge blocks of canonical vacancy components

This file transports the canonical king-component partition to the explicit
rectangular primal graph and proves that the corresponding dual edge-label
blocks are disjoint.  Parallel dual edges remain distinct labels.
-/

set_option autoImplicit false

namespace SquareMaximality
namespace Dual

open Multigraph

private theorem boundary_subset_grid (R S : ℕ) (A : Finset Point) :
    Boundary.boundaryVacancies R S (Boundary.canonicalVacancies R S A) ⊆
      Boundary.grid R S :=
  (Boundary.boundaryVacancies_subset R S _).trans
    (encodedVacancies_subset_grid R S A)

private theorem canonicalInterior_subset_grid (R S : ℕ) (A : Finset Point)
    (i : Fin (Boundary.canonicalInteriorCount R S A)) :
    Boundary.interiorComponent R S (Boundary.canonicalVacancies R S A)
        ((Boundary.canonicalInteriorEquiv R S A).symm i) ⊆
      Boundary.grid R S :=
  (Boundary.interiorComponent_subset_interiorVacancies R S _ _).trans
    ((Boundary.interiorVacancies_subset R S _).trans
      (encodedVacancies_subset_grid R S A))

/-- Boundary-attached vacancies as vertices of the explicit primal graph. -/
noncomputable def canonicalBoundaryPrimal (R S : ℕ) (A : Finset Point) :
    Finset (Fin (R + 1) × Fin (S + 1)) :=
  toPrimalVertices R S
    (Boundary.boundaryVacancies R S (Boundary.canonicalVacancies R S A))
    (boundary_subset_grid R S A)

/-- One interior vacancy component as explicit primal vertices. -/
noncomputable def canonicalInteriorPrimal (R S : ℕ) (A : Finset Point)
    (i : Fin (Boundary.canonicalInteriorCount R S A)) :
    Finset (Fin (R + 1) × Fin (S + 1)) :=
  toPrimalVertices R S
    (Boundary.interiorComponent R S (Boundary.canonicalVacancies R S A)
      ((Boundary.canonicalInteriorEquiv R S A).symm i))
    (canonicalInterior_subset_grid R S A i)

@[simp] theorem mem_canonicalBoundaryPrimal
    {R S : ℕ} {A : Finset Point} {p : Fin (R + 1) × Fin (S + 1)} :
    p ∈ canonicalBoundaryPrimal R S A ↔
      finPoint p ∈
        Boundary.boundaryVacancies R S (Boundary.canonicalVacancies R S A) :=
  mem_toPrimalVertices (boundary_subset_grid R S A)

@[simp] theorem mem_canonicalInteriorPrimal
    {R S : ℕ} {A : Finset Point}
    {i : Fin (Boundary.canonicalInteriorCount R S A)}
    {p : Fin (R + 1) × Fin (S + 1)} :
    p ∈ canonicalInteriorPrimal R S A i ↔
      finPoint p ∈ Boundary.interiorComponent R S
        (Boundary.canonicalVacancies R S A)
        ((Boundary.canonicalInteriorEquiv R S A).symm i) :=
  mem_toPrimalVertices (canonicalInterior_subset_grid R S A i)

theorem kingSeparated_boundary_interior
    (R S : ℕ) (A : Finset Point)
    (i : Fin (Boundary.canonicalInteriorCount R S A))
    (p : Fin (R + 1) × Fin (S + 1)) (hp : p ∈ canonicalBoundaryPrimal R S A)
    (q : Fin (R + 1) × Fin (S + 1)) (hq : q ∈ canonicalInteriorPrimal R S A i) :
    p ≠ q ∧ ¬Boundary.KingAdjacent (finPoint p) (finPoint q) := by
  let V := Boundary.canonicalVacancies R S A
  have hpB : finPoint p ∈ Boundary.boundaryVacancies R S V :=
    mem_canonicalBoundaryPrimal.mp hp
  have hqC : finPoint q ∈ Boundary.interiorComponent R S V
      ((Boundary.canonicalInteriorEquiv R S A).symm i) :=
    mem_canonicalInteriorPrimal.mp hq
  have hqI : finPoint q ∈ Boundary.interiorVacancies R S V :=
    Boundary.interiorComponent_subset_interiorVacancies R S V _ hqC
  constructor
  · intro hpq
    subst q
    exact Finset.disjoint_left.mp
      (Boundary.boundaryVacancies_disjoint_interiorVacancies R S V) hpB hqI
  · intro hadj
    have hpV : finPoint p ∈ V := Boundary.boundaryVacancies_subset R S V hpB
    have hqV : finPoint q ∈ V := Boundary.interiorVacancies_subset R S V hqI
    have hreach : (Boundary.kingGraph V).Reachable
        ⟨finPoint p, hpV⟩ ⟨finPoint q, hqV⟩ := by
      apply SimpleGraph.Adj.reachable
      exact (Boundary.kingGraph_adj_iff _ _).mpr hadj
    have hpAttached : Boundary.IsBoundaryAttached R S V (finPoint p) :=
      Boundary.mem_boundaryVacancies.mp hpB
    have hqAttached := Boundary.isBoundaryAttached_of_reachable hpAttached hreach
    exact (Boundary.mem_interiorVacancies.mp hqI).2 hqAttached

theorem kingSeparated_interior
    (R S : ℕ) (A : Finset Point)
    {i j : Fin (Boundary.canonicalInteriorCount R S A)} (hij : i ≠ j)
    (p : Fin (R + 1) × Fin (S + 1)) (hp : p ∈ canonicalInteriorPrimal R S A i)
    (q : Fin (R + 1) × Fin (S + 1)) (hq : q ∈ canonicalInteriorPrimal R S A j) :
    p ≠ q ∧ ¬Boundary.KingAdjacent (finPoint p) (finPoint q) := by
  let V := Boundary.canonicalVacancies R S A
  let ci := (Boundary.canonicalInteriorEquiv R S A).symm i
  let cj := (Boundary.canonicalInteriorEquiv R S A).symm j
  have hpC : finPoint p ∈ Boundary.interiorComponent R S V ci :=
    mem_canonicalInteriorPrimal.mp hp
  have hqC : finPoint q ∈ Boundary.interiorComponent R S V cj :=
    mem_canonicalInteriorPrimal.mp hq
  have hcij : ci ≠ cj := by
    intro h
    apply hij
    exact (Boundary.canonicalInteriorEquiv R S A).symm.injective h
  constructor
  · intro hpq
    subst q
    exact Finset.disjoint_left.mp
      (Boundary.interiorComponents_pairwiseDisjoint R S V hcij) hpC hqC
  · intro hadj
    rcases Boundary.mem_interiorComponent.mp hpC with ⟨hpV, hpClass⟩
    rcases Boundary.mem_interiorComponent.mp hqC with ⟨hqV, hqClass⟩
    have hgraphAdj : (Boundary.kingGraph V).Adj
        ⟨finPoint p, hpV⟩ ⟨finPoint q, hqV⟩ :=
      (Boundary.kingGraph_adj_iff _ _).mpr hadj
    have hclasses := SimpleGraph.ConnectedComponent.sound hgraphAdj.reachable
    apply hcij
    apply Subtype.ext
    exact hpClass.symm.trans (hclasses.trans hqClass)

/-- The boundary dual edge block is disjoint from each interior block. -/
theorem disjoint_boundary_interior_dualEdges
    (R S : ℕ) (A : Finset Point)
    (i : Fin (Boundary.canonicalInteriorCount R S A)) :
    Disjoint (vacancyDualEdges (canonicalBoundaryPrimal R S A))
      (vacancyDualEdges (canonicalInteriorPrimal R S A i)) := by
  apply disjoint_vacancyDualEdges_of_kingSeparated
  exact kingSeparated_boundary_interior R S A i

/-- Distinct interior components generate disjoint dual edge-label blocks. -/
theorem disjoint_interior_dualEdges
    (R S : ℕ) (A : Finset Point)
    {i j : Fin (Boundary.canonicalInteriorCount R S A)} (hij : i ≠ j) :
    Disjoint (vacancyDualEdges (canonicalInteriorPrimal R S A i))
      (vacancyDualEdges (canonicalInteriorPrimal R S A j)) := by
  apply disjoint_vacancyDualEdges_of_kingSeparated
  exact kingSeparated_interior R S A hij

/-- The explicit primal vacancy set is exactly the boundary block plus all
interior king-component blocks. -/
theorem encodedPrimalVacancies_partition (R S : ℕ) (A : Finset Point) :
    encodedPrimalVacancies R S A =
      canonicalBoundaryPrimal R S A ∪
        Finset.univ.biUnion (canonicalInteriorPrimal R S A) := by
  classical
  ext p
  rw [mem_encodedPrimalVacancies]
  constructor
  · intro hpV
    by_cases hpB : finPoint p ∈
        Boundary.boundaryVacancies R S (Boundary.canonicalVacancies R S A)
    · exact Finset.mem_union.mpr (Or.inl (mem_canonicalBoundaryPrimal.mpr hpB))
    · have hpI : finPoint p ∈
          Boundary.interiorVacancies R S (Boundary.canonicalVacancies R S A) :=
        Boundary.mem_interiorVacancies.mpr ⟨hpV, by
          simpa [Boundary.mem_boundaryVacancies] using hpB⟩
      rw [← Boundary.allInteriorComponents_eq R S
        (Boundary.canonicalVacancies R S A)] at hpI
      rcases Finset.mem_biUnion.mp hpI with ⟨c, _, hpc⟩
      let i := Boundary.canonicalInteriorEquiv R S A c
      apply Finset.mem_union.mpr
      right
      apply Finset.mem_biUnion.mpr
      refine ⟨i, Finset.mem_univ _, ?_⟩
      apply mem_canonicalInteriorPrimal.mpr
      simpa [i] using hpc
  · intro hp
    rcases Finset.mem_union.mp hp with hpB | hpI
    · exact Boundary.boundaryVacancies_subset R S _
        (mem_canonicalBoundaryPrimal.mp hpB)
    · rcases Finset.mem_biUnion.mp hpI with ⟨i, _, hpi⟩
      exact Boundary.interiorVacancies_subset R S _
        (Boundary.interiorComponent_subset_interiorVacancies R S _ _
          (mem_canonicalInteriorPrimal.mp hpi))

/-- One indexed family containing the boundary dual block (`none`) and every
interior dual block (`some i`). -/
noncomputable def canonicalDualEdgeBlock (R S : ℕ) (A : Finset Point) :
    Option (Fin (Boundary.canonicalInteriorCount R S A)) →
      Finset (RectangleEdge (R + 1) (S + 1))
  | none => vacancyDualEdges (canonicalBoundaryPrimal R S A)
  | some i => vacancyDualEdges (canonicalInteriorPrimal R S A i)

/-- The canonical dual edge blocks are pairwise label-disjoint. -/
theorem canonicalDualEdgeBlock_pairwiseDisjoint (R S : ℕ) (A : Finset Point) :
    Pairwise fun i j =>
      Disjoint (canonicalDualEdgeBlock R S A i) (canonicalDualEdgeBlock R S A j) := by
  intro i j hij
  cases i with
  | none =>
      cases j with
      | none => exact (hij rfl).elim
      | some j => exact disjoint_boundary_interior_dualEdges R S A j
  | some i =>
      cases j with
      | none => exact (disjoint_boundary_interior_dualEdges R S A i).symm
      | some j =>
          apply disjoint_interior_dualEdges R S A
          intro h
          exact hij (congrArg some h)

/-- Taking the union of all canonical blocks recovers precisely the dual
labels incident with at least one vacancy. -/
theorem unionEdgeBlocks_canonicalDualEdgeBlock (R S : ℕ) (A : Finset Point) :
    Multigraph.LabeledMultigraph.unionEdgeBlocks (canonicalDualEdgeBlock R S A) =
      vacancyDualEdges (encodedPrimalVacancies R S A) := by
  classical
  ext e
  rw [Multigraph.LabeledMultigraph.mem_unionEdgeBlocks]
  constructor
  · rintro ⟨i, hi⟩
    apply mem_vacancyDualEdges.mpr
    cases i with
    | none =>
        rcases mem_vacancyDualEdges.mp hi with ⟨p, hp, hpe⟩
        exact ⟨p, encodedPrimalVacancies_partition R S A ▸
          Finset.mem_union_left _ hp, hpe⟩
    | some i =>
        rcases mem_vacancyDualEdges.mp hi with ⟨p, hp, hpe⟩
        have hpUnion : p ∈ canonicalBoundaryPrimal R S A ∪
            Finset.univ.biUnion (canonicalInteriorPrimal R S A) := by
          apply Finset.mem_union.mpr
          right
          exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hp⟩
        exact ⟨p, (encodedPrimalVacancies_partition R S A).symm ▸ hpUnion, hpe⟩
  · intro he
    rcases mem_vacancyDualEdges.mp he with ⟨p, hp, hpe⟩
    have hpPart := (encodedPrimalVacancies_partition R S A) ▸ hp
    rcases Finset.mem_union.mp hpPart with hpB | hpI
    · exact ⟨none, mem_vacancyDualEdges.mpr ⟨p, hpB, hpe⟩⟩
    · rcases Finset.mem_biUnion.mp hpI with ⟨i, _, hpi⟩
      exact ⟨some i, mem_vacancyDualEdges.mpr ⟨p, hpi, hpe⟩⟩

end Dual
end SquareMaximality
