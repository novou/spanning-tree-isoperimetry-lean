module

public import SquareMaximality.Boundary.Encoding

@[expose] public section

set_option autoImplicit false

/-!
# King-adjacency vacancy components

This file defines the exact component partition used in `general.tex`, lines
640--673: vacancies which can reach the rectangular perimeter by king moves,
and the complementary interior vacancies.  The definitions are finite and all
partition/closure facts below are proved without graph-duality assumptions.
-/

namespace SquareMaximality

namespace Boundary

/-- Two natural-coordinate lattice points differ by one king move. -/
def KingAdjacent (p q : LatticePoint) : Prop :=
  p ≠ q ∧ Nat.dist p.1 q.1 ≤ 1 ∧ Nat.dist p.2 q.2 ≤ 1

theorem kingAdjacent_symm : Std.Symm KingAdjacent := by
  constructor
  intro p q h
  exact ⟨h.1.symm, by simpa [Nat.dist_comm] using h.2.1,
    by simpa [Nat.dist_comm] using h.2.2⟩

theorem kingAdjacent_irrefl : Std.Irrefl KingAdjacent := by
  constructor
  intro p h
  exact h.1 rfl

/-- King graph induced by a finite vacancy set. -/
def kingGraph (V : Finset LatticePoint) : SimpleGraph {p // p ∈ V} :=
  SimpleGraph.fromRel fun p q => KingAdjacent p.1 q.1

@[simp] theorem kingGraph_adj_iff {V : Finset LatticePoint}
    (p q : {z // z ∈ V}) :
    (kingGraph V).Adj p q ↔ KingAdjacent p.1 q.1 := by
  simp only [kingGraph, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨_hpq, hpq | hqp⟩
    · exact hpq
    · exact @Std.Symm.symm _ _ kingAdjacent_symm q.1 p.1 hqp
  · intro hpq
    exact ⟨fun h => hpq.1 (Subtype.ext_iff.mp h), Or.inl hpq⟩

/-- Perimeter of the natural-coordinate grid `{0,...,R} × {0,...,S}`. -/
def IsPerimeter (R S : ℕ) (p : LatticePoint) : Prop :=
  p.1 = 0 ∨ p.1 = R ∨ p.2 = 0 ∨ p.2 = S

/-- A vacancy is boundary-attached when its king component meets the perimeter. -/
def IsBoundaryAttached (R S : ℕ) (V : Finset LatticePoint)
    (p : LatticePoint) : Prop :=
  ∃ hp : p ∈ V, ∃ q : {z // z ∈ V},
    IsPerimeter R S q.1 ∧
      (kingGraph V).Reachable ⟨p, hp⟩ q

/-- Union of all king components meeting the perimeter. -/
noncomputable def boundaryVacancies (R S : ℕ) (V : Finset LatticePoint) :
    Finset LatticePoint := by
  classical
  exact V.filter fun p => IsBoundaryAttached R S V p

/-- Union of the remaining, interior king components. -/
noncomputable def interiorVacancies (R S : ℕ) (V : Finset LatticePoint) :
    Finset LatticePoint :=
  V \ boundaryVacancies R S V

@[simp] theorem mem_boundaryVacancies {R S : ℕ} {V : Finset LatticePoint}
    {p : LatticePoint} :
    p ∈ boundaryVacancies R S V ↔ IsBoundaryAttached R S V p := by
  classical
  constructor
  · intro hp
    exact (Finset.mem_filter.mp hp).2
  · intro hp
    exact Finset.mem_filter.mpr ⟨by rcases hp with ⟨hpV, _⟩; exact hpV, hp⟩

@[simp] theorem mem_interiorVacancies {R S : ℕ} {V : Finset LatticePoint}
    {p : LatticePoint} :
    p ∈ interiorVacancies R S V ↔ p ∈ V ∧ ¬IsBoundaryAttached R S V p := by
  classical
  simp [interiorVacancies]

theorem boundaryVacancies_subset (R S : ℕ) (V : Finset LatticePoint) :
    boundaryVacancies R S V ⊆ V := by
  classical
  exact Finset.filter_subset _ _

theorem interiorVacancies_subset (R S : ℕ) (V : Finset LatticePoint) :
    interiorVacancies R S V ⊆ V :=
  Finset.sdiff_subset

theorem boundaryVacancies_disjoint_interiorVacancies
    (R S : ℕ) (V : Finset LatticePoint) :
    Disjoint (boundaryVacancies R S V) (interiorVacancies R S V) := by
  exact Finset.disjoint_sdiff

theorem boundaryVacancies_union_interiorVacancies
    (R S : ℕ) (V : Finset LatticePoint) :
    boundaryVacancies R S V ∪ interiorVacancies R S V = V := by
  classical
  rw [Finset.union_comm]
  exact Finset.sdiff_union_of_subset (boundaryVacancies_subset R S V)

theorem card_boundaryVacancies_add_card_interiorVacancies
    (R S : ℕ) (V : Finset LatticePoint) :
    (boundaryVacancies R S V).card + (interiorVacancies R S V).card = V.card := by
  calc
    (boundaryVacancies R S V).card + (interiorVacancies R S V).card =
        (boundaryVacancies R S V ∪ interiorVacancies R S V).card :=
      (Finset.card_union_of_disjoint
        (boundaryVacancies_disjoint_interiorVacancies R S V)).symm
    _ = V.card := congrArg Finset.card
      (boundaryVacancies_union_interiorVacancies R S V)

/-- A vacant perimeter point is boundary-attached by a zero-length path. -/
theorem isBoundaryAttached_of_perimeter
    {R S : ℕ} {V : Finset LatticePoint} {p : LatticePoint}
    (hpV : p ∈ V) (hp : IsPerimeter R S p) :
    IsBoundaryAttached R S V p := by
  exact ⟨hpV, ⟨p, hpV⟩, hp, SimpleGraph.Reachable.refl _⟩

/-- Boundary attachment is constant along king-reachability classes. -/
theorem isBoundaryAttached_of_reachable
    {R S : ℕ} {V : Finset LatticePoint}
    {p q : {z // z ∈ V}}
    (hp : IsBoundaryAttached R S V p.1)
    (hpq : (kingGraph V).Reachable p q) :
    IsBoundaryAttached R S V q.1 := by
  rcases hp with ⟨_hpV, z, hzPerim, hpz⟩
  exact ⟨q.2, z, hzPerim, hpq.symm.trans hpz⟩

theorem isBoundaryAttached_iff_of_reachable
    {R S : ℕ} {V : Finset LatticePoint}
    {p q : {z // z ∈ V}}
    (hpq : (kingGraph V).Reachable p q) :
    IsBoundaryAttached R S V p.1 ↔ IsBoundaryAttached R S V q.1 := by
  exact ⟨fun hp => isBoundaryAttached_of_reachable hp hpq,
    fun hq => isBoundaryAttached_of_reachable hq hpq.symm⟩

/-- An interior vacancy cannot reach any vacant perimeter point. -/
theorem interior_not_reachable_perimeter
    {R S : ℕ} {V : Finset LatticePoint}
    {p : LatticePoint} (hp : p ∈ interiorVacancies R S V)
    {q : {z // z ∈ V}} (hqPerim : IsPerimeter R S q.1) :
    ¬(kingGraph V).Reachable ⟨p, (mem_interiorVacancies.mp hp).1⟩ q := by
  intro hpq
  exact (mem_interiorVacancies.mp hp).2
    ⟨(mem_interiorVacancies.mp hp).1, q, hqPerim, hpq⟩

end Boundary

end SquareMaximality
