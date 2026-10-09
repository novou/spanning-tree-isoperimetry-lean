import SquareMaximality.Dual.Vacancies
import SquareMaximality.Boundary.Encoding

/-!
# Coordinate bridge for rectangular primal vertices

The boundary development uses natural-coordinate points in a finite grid,
whereas the explicit rectangular primal graph uses `Fin` coordinates.  This
file gives the exact finite equivalence and transports vacancy finsets without
changing membership or cardinality.
-/

set_option autoImplicit false

namespace SquareMaximality
namespace Dual

/-- `Fin` coordinates of an `(R+1) × (S+1)` primal rectangle are exactly the
natural points of `Boundary.grid R S`. -/
def finGridEquiv (R S : ℕ) :
    (Fin (R + 1) × Fin (S + 1)) ≃ {z // z ∈ Boundary.grid R S} where
  toFun p := ⟨finPoint p, by
    rw [Boundary.mem_grid]
    exact ⟨Nat.le_of_lt_succ p.1.2, Nat.le_of_lt_succ p.2.2⟩⟩
  invFun z :=
    (⟨z.1.1, Nat.lt_succ_of_le (Boundary.mem_grid.mp z.2).1⟩,
      ⟨z.1.2, Nat.lt_succ_of_le (Boundary.mem_grid.mp z.2).2⟩)
  left_inv p := by
    apply Prod.ext <;> apply Fin.ext <;> rfl
  right_inv z := by
    apply Subtype.ext
    rfl

@[simp] theorem finGridEquiv_apply (R S : ℕ) (p : Fin (R + 1) × Fin (S + 1)) :
    (finGridEquiv R S p).1 = finPoint p := rfl

@[simp] theorem finPoint_finGridEquiv_symm
    (R S : ℕ) (z : {z // z ∈ Boundary.grid R S}) :
    finPoint ((finGridEquiv R S).symm z) = z.1 := by
  exact congrArg Subtype.val ((finGridEquiv R S).apply_symm_apply z)

/-- Transport a finite in-grid natural-coordinate set to the explicit primal
vertex type. -/
noncomputable def toPrimalVertices (R S : ℕ) (V : Finset Boundary.LatticePoint)
    (hV : V ⊆ Boundary.grid R S) : Finset (Fin (R + 1) × Fin (S + 1)) := by
  classical
  exact V.attach.image fun z =>
    (finGridEquiv R S).symm ⟨z.1, hV z.2⟩

@[simp] theorem mem_toPrimalVertices
    {R S : ℕ} {V : Finset Boundary.LatticePoint}
    (hV : V ⊆ Boundary.grid R S)
    {p : Fin (R + 1) × Fin (S + 1)} :
    p ∈ toPrimalVertices R S V hV ↔ finPoint p ∈ V := by
  classical
  constructor
  · intro hp
    rcases Finset.mem_image.mp hp with ⟨z, _, hzp⟩
    have := congrArg finPoint hzp
    simpa using this.symm ▸ z.2
  · intro hp
    apply Finset.mem_image.mpr
    refine ⟨⟨finPoint p, hp⟩, Finset.mem_attach _ _, ?_⟩
    apply (finGridEquiv R S).injective
    apply Subtype.ext
    simp

theorem image_toPrimalVertices_finPoint
    (R S : ℕ) (V : Finset Boundary.LatticePoint)
    (hV : V ⊆ Boundary.grid R S) :
    (toPrimalVertices R S V hV).image finPoint = V := by
  classical
  ext z
  constructor
  · intro hz
    rcases Finset.mem_image.mp hz with ⟨p, hp, hpz⟩
    exact hpz ▸ (mem_toPrimalVertices hV).mp hp
  · intro hz
    let p : Fin (R + 1) × Fin (S + 1) :=
      (finGridEquiv R S).symm ⟨z, hV hz⟩
    have hpz : finPoint p = z := by simp [p]
    exact Finset.mem_image.mpr ⟨p,
      (mem_toPrimalVertices hV).mpr (hpz.symm ▸ hz), hpz⟩

@[simp] theorem card_toPrimalVertices
    (R S : ℕ) (V : Finset Boundary.LatticePoint)
    (hV : V ⊆ Boundary.grid R S) :
    (toPrimalVertices R S V hV).card = V.card := by
  calc
    (toPrimalVertices R S V hV).card =
        ((toPrimalVertices R S V hV).image finPoint).card :=
      (Finset.card_image_of_injective _ finPoint_injective).symm
    _ = V.card := congrArg Finset.card
      (image_toPrimalVertices_finPoint R S V hV)

theorem encodedVacancies_subset_grid (R S : ℕ) (A : Finset Point) :
    Boundary.encodedVacancies R S A ⊆ Boundary.grid R S := by
  intro z hz
  exact Finset.mem_filter.mp hz |>.1

/-- Canonical encoded vacancies, as vertices of the explicit primal graph. -/
noncomputable def encodedPrimalVacancies (R S : ℕ) (A : Finset Point) :
    Finset (Fin (R + 1) × Fin (S + 1)) :=
  toPrimalVertices R S (Boundary.encodedVacancies R S A)
    (encodedVacancies_subset_grid R S A)

@[simp] theorem mem_encodedPrimalVacancies
    {R S : ℕ} {A : Finset Point} {p : Fin (R + 1) × Fin (S + 1)} :
    p ∈ encodedPrimalVacancies R S A ↔
      finPoint p ∈ Boundary.encodedVacancies R S A := by
  exact mem_toPrimalVertices (encodedVacancies_subset_grid R S A)

@[simp] theorem card_encodedPrimalVacancies (R S : ℕ) (A : Finset Point) :
    (encodedPrimalVacancies R S A).card =
      (Boundary.encodedVacancies R S A).card :=
  card_toPrimalVertices R S _ _

end Dual
end SquareMaximality
