module

public import SquareMaximality.Boundary.King

@[expose] public section

/-!
# Finite enumeration of interior king components

This module turns the quotient of vacancies by king reachability into the
finite indexed family `J₁,…,Jₘ` used in the hull proof.  The boundary-attached
union and these interior components form an exact, pairwise-disjoint
partition, including the case of no interior components.
-/

set_option autoImplicit false

namespace SquareMaximality
namespace Boundary

open SimpleGraph

/-- Connected-component classes represented by an interior vacancy. -/
noncomputable def interiorComponentClasses (R S : ℕ) (V : Finset LatticePoint) :
    Finset (kingGraph V).ConnectedComponent := by
  classical
  exact (interiorVacancies R S V).attach.image fun p =>
    (kingGraph V).connectedComponentMk
      ⟨p.1, interiorVacancies_subset R S V p.2⟩

/-- Finite index type for the interior king components. -/
abbrev InteriorComponentIndex (R S : ℕ) (V : Finset LatticePoint) :=
  {c : (kingGraph V).ConnectedComponent // c ∈ interiorComponentClasses R S V}

/-- All vacancy points in one indexed interior king component. -/
noncomputable def interiorComponent (R S : ℕ) (V : Finset LatticePoint)
    (c : InteriorComponentIndex R S V) : Finset LatticePoint := by
  classical
  exact (Finset.univ.filter fun p : {z // z ∈ V} =>
    (kingGraph V).connectedComponentMk p = c.1).image Subtype.val

@[simp] theorem mem_interiorComponent
    {R S : ℕ} {V : Finset LatticePoint}
    {c : InteriorComponentIndex R S V} {p : LatticePoint} :
    p ∈ interiorComponent R S V c ↔
      ∃ hp : p ∈ V, (kingGraph V).connectedComponentMk ⟨p, hp⟩ = c.1 := by
  classical
  simp [interiorComponent]

theorem interiorComponent_nonempty
    (R S : ℕ) (V : Finset LatticePoint)
    (c : InteriorComponentIndex R S V) :
    (interiorComponent R S V c).Nonempty := by
  classical
  rcases Finset.mem_image.mp c.2 with ⟨p, hp, hpc⟩
  have hpV : p.1 ∈ V := interiorVacancies_subset R S V p.2
  refine ⟨p.1, mem_interiorComponent.mpr ⟨hpV, ?_⟩⟩
  exact hpc

theorem interiorComponent_subset_interiorVacancies
    (R S : ℕ) (V : Finset LatticePoint)
    (c : InteriorComponentIndex R S V) :
    interiorComponent R S V c ⊆ interiorVacancies R S V := by
  classical
  rcases Finset.mem_image.mp c.2 with ⟨p, hp, hpc⟩
  have hpV : p.1 ∈ V := interiorVacancies_subset R S V p.2
  intro q hq
  rcases mem_interiorComponent.mp hq with ⟨hqV, hqc⟩
  have heq : (kingGraph V).connectedComponentMk ⟨q, hqV⟩ =
      (kingGraph V).connectedComponentMk ⟨p.1, hpV⟩ := hqc.trans hpc.symm
  have hreach : (kingGraph V).Reachable ⟨q, hqV⟩ ⟨p.1, hpV⟩ :=
    ConnectedComponent.exact heq
  have hnotBoundary : ¬IsBoundaryAttached R S V q := by
    intro hqBoundary
    have hpBoundary := isBoundaryAttached_of_reachable hqBoundary hreach
    exact (mem_interiorVacancies.mp p.2).2 hpBoundary
  exact mem_interiorVacancies.mpr ⟨hqV, hnotBoundary⟩

theorem interiorComponents_pairwiseDisjoint (R S : ℕ) (V : Finset LatticePoint) :
    Pairwise fun c d : InteriorComponentIndex R S V =>
      Disjoint (interiorComponent R S V c) (interiorComponent R S V d) := by
  classical
  intro c d hcd
  rw [Finset.disjoint_left]
  intro p hpc hpd
  rcases mem_interiorComponent.mp hpc with ⟨hpV, hpcClass⟩
  rcases mem_interiorComponent.mp hpd with ⟨_, hpdClass⟩
  apply hcd
  apply Subtype.ext
  exact hpcClass.symm.trans hpdClass

/-- The union of all indexed interior components. -/
noncomputable def allInteriorComponents (R S : ℕ) (V : Finset LatticePoint) :
    Finset LatticePoint := by
  classical
  exact Finset.univ.biUnion (interiorComponent R S V)

theorem allInteriorComponents_eq (R S : ℕ) (V : Finset LatticePoint) :
    allInteriorComponents R S V = interiorVacancies R S V := by
  classical
  apply Finset.Subset.antisymm
  · intro p hp
    rcases Finset.mem_biUnion.mp hp with ⟨c, _, hpc⟩
    exact interiorComponent_subset_interiorVacancies R S V c hpc
  · intro p hp
    let pV : {z // z ∈ V} := ⟨p, interiorVacancies_subset R S V hp⟩
    have hclass : (kingGraph V).connectedComponentMk pV ∈
        interiorComponentClasses R S V := by
      apply Finset.mem_image.mpr
      exact ⟨⟨p, hp⟩, Finset.mem_attach _ _, rfl⟩
    let c : InteriorComponentIndex R S V :=
      ⟨(kingGraph V).connectedComponentMk pV, hclass⟩
    apply Finset.mem_biUnion.mpr
    exact ⟨c, Finset.mem_univ _, mem_interiorComponent.mpr ⟨pV.2, rfl⟩⟩

theorem card_interiorComponents (R S : ℕ) (V : Finset LatticePoint) :
    ∑ c : InteriorComponentIndex R S V, (interiorComponent R S V c).card =
      (interiorVacancies R S V).card := by
  classical
  rw [← allInteriorComponents_eq R S V, allInteriorComponents,
    Finset.card_biUnion]
  intro c _ d _ hcd
  exact interiorComponents_pairwiseDisjoint R S V hcd

/-- Exact vacancy partition into the boundary-attached union and the indexed
interior components. -/
theorem card_boundary_add_interiorComponents
    (R S : ℕ) (V : Finset LatticePoint) :
    (boundaryVacancies R S V).card +
        ∑ c : InteriorComponentIndex R S V,
          (interiorComponent R S V c).card = V.card := by
  rw [card_interiorComponents, card_boundaryVacancies_add_card_interiorVacancies]

end Boundary
end SquareMaximality
