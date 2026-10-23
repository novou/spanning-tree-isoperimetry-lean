module

public import SquareMaximality.Boundary.Components
public import SquareMaximality.Boundary.Assembly

@[expose] public section

/-!
# Canonical hull-factor data

The abstract assembly theorem accepts an arbitrary component decomposition.
Here we construct that decomposition canonically from the king components of
the encoded vacancy set.  Consequently the remaining inputs are exactly the
component-product, boundary-factor, and interior-factor inequalities.
-/

set_option autoImplicit false

namespace SquareMaximality
namespace Boundary

/-- Encoded vacancies for an integer-lattice set in an `(R+1) × (S+1)`
standard rectangle. -/
abbrev canonicalVacancies (R S : ℕ) (A : Finset Point) : Finset LatticePoint :=
  encodedVacancies R S A

/-- Canonical number of interior king components. -/
noncomputable def canonicalInteriorCount (R S : ℕ) (A : Finset Point) : ℕ :=
  Fintype.card (InteriorComponentIndex R S (canonicalVacancies R S A))

/-- Canonical equivalence used only to present the finite component family as
`Fin m`, matching `HullFactorData`. -/
noncomputable def canonicalInteriorEquiv (R S : ℕ) (A : Finset Point) :
    InteriorComponentIndex R S (canonicalVacancies R S A) ≃
      Fin (canonicalInteriorCount R S A) :=
  Fintype.equivFin _

/-- Boundary-attached vacancy points, returned to integer coordinates. -/
noncomputable def canonicalBoundary (R S : ℕ) (A : Finset Point) : Finset Point :=
  (boundaryVacancies R S (canonicalVacancies R S A)).image ofNatPoint

/-- One interior king component, returned to integer coordinates. -/
noncomputable def canonicalInterior (R S : ℕ) (A : Finset Point)
    (i : Fin (canonicalInteriorCount R S A)) : Finset Point :=
  (interiorComponent R S (canonicalVacancies R S A)
    ((canonicalInteriorEquiv R S A).symm i)).image ofNatPoint

theorem canonicalBoundary_disjoint_interiorUnion (R S : ℕ) (A : Finset Point) :
    Disjoint (canonicalBoundary R S A)
      (Finset.univ.biUnion (canonicalInterior R S A)) := by
  classical
  rw [Finset.disjoint_left]
  intro p hpB hpI
  rcases Finset.mem_image.mp hpB with ⟨z, hzB, hzp⟩
  rcases Finset.mem_biUnion.mp hpI with ⟨i, _, hpi⟩
  rcases Finset.mem_image.mp hpi with ⟨w, hwI, hwp⟩
  have hzw : z = w := ofNatPoint_injective (hzp.trans hwp.symm)
  subst w
  have hzInterior := interiorComponent_subset_interiorVacancies R S
    (canonicalVacancies R S A) ((canonicalInteriorEquiv R S A).symm i) hwI
  exact Finset.disjoint_left.mp
    (boundaryVacancies_disjoint_interiorVacancies R S (canonicalVacancies R S A))
    hzB hzInterior

theorem canonicalInterior_pairwise (R S : ℕ) (A : Finset Point) :
    ((Finset.univ : Finset (Fin (canonicalInteriorCount R S A))) :
      Set (Fin (canonicalInteriorCount R S A))).PairwiseDisjoint
        (canonicalInterior R S A) := by
  classical
  intro i _ j _ hij
  change Disjoint (canonicalInterior R S A i) (canonicalInterior R S A j)
  rw [Finset.disjoint_left]
  intro p hpi hpj
  rcases Finset.mem_image.mp hpi with ⟨z, hzi, hzp⟩
  rcases Finset.mem_image.mp hpj with ⟨w, hwj, hwp⟩
  have hzw : z = w := ofNatPoint_injective (hzp.trans hwp.symm)
  subst w
  have hindex : (canonicalInteriorEquiv R S A).symm i ≠
      (canonicalInteriorEquiv R S A).symm j := by
    intro h
    apply hij
    exact (canonicalInteriorEquiv R S A).symm.injective h
  exact Finset.disjoint_left.mp
    (interiorComponents_pairwiseDisjoint R S (canonicalVacancies R S A) hindex)
    hzi hwj

theorem canonicalInteriorUnion_eq (R S : ℕ) (A : Finset Point) :
    Finset.univ.biUnion (canonicalInterior R S A) =
      (interiorVacancies R S (canonicalVacancies R S A)).image ofNatPoint := by
  classical
  ext p
  constructor
  · intro hp
    rcases Finset.mem_biUnion.mp hp with ⟨i, _, hpi⟩
    rcases Finset.mem_image.mp hpi with ⟨z, hzi, rfl⟩
    exact Finset.mem_image.mpr ⟨z,
      interiorComponent_subset_interiorVacancies R S
        (canonicalVacancies R S A) ((canonicalInteriorEquiv R S A).symm i) hzi,
      rfl⟩
  · intro hp
    rcases Finset.mem_image.mp hp with ⟨z, hzI, rfl⟩
    rw [← allInteriorComponents_eq R S (canonicalVacancies R S A)] at hzI
    rcases Finset.mem_biUnion.mp hzI with ⟨c, _, hzc⟩
    let i := canonicalInteriorEquiv R S A c
    apply Finset.mem_biUnion.mpr
    refine ⟨i, Finset.mem_univ _, ?_⟩
    apply Finset.mem_image.mpr
    refine ⟨z, ?_, rfl⟩
    simpa [i] using hzc

theorem canonical_partition (R S : ℕ) (A : Finset Point) :
    rectangle 0 0 (R + 1) (S + 1) \ A =
      canonicalBoundary R S A ∪
        Finset.univ.biUnion (canonicalInterior R S A) := by
  classical
  rw [← image_encodedVacancies R S A, canonicalInteriorUnion_eq, canonicalBoundary]
  rw [← Finset.image_union]
  exact congrArg (Finset.image ofNatPoint)
    (boundaryVacancies_union_interiorVacancies R S (canonicalVacancies R S A)).symm

/-- The only three substantive estimates remaining after choosing the
canonical component decomposition. -/
structure CanonicalFactorEstimates (κ : ℝ) (A : Finset Point) (R S : ℕ) : Prop where
  componentProduct :
    Real.log (tau A : ℝ) - Real.log (tauRect (R + 1) (S + 1) : ℝ) ≤
      (Real.log (tau (rectangle 0 0 (R + 1) (S + 1) \
          canonicalBoundary R S A) : ℝ) -
        Real.log (tauRect (R + 1) (S + 1) : ℝ)) +
      ∑ i, (Real.log (tau (rectangle 0 0 (R + 1) (S + 1) \
          canonicalInterior R S A i) : ℝ) -
        Real.log (tauRect (R + 1) (S + 1) : ℝ))
  boundaryFactor :
    Real.log (tau (rectangle 0 0 (R + 1) (S + 1) \
        canonicalBoundary R S A) : ℝ) -
      Real.log (tauRect (R + 1) (S + 1) : ℝ) ≤
        -κ * (canonicalBoundary R S A).card
  interiorFactor : ∀ i,
    Real.log (tau (rectangle 0 0 (R + 1) (S + 1) \
        canonicalInterior R S A i) : ℝ) -
      Real.log (tauRect (R + 1) (S + 1) : ℝ) ≤
        -κ * (canonicalInterior R S A i).card

namespace CanonicalFactorEstimates

variable {κ : ℝ} {A : Finset Point} {R S : ℕ}

/-- Canonical estimates produce the abstract factor data with no additional
partition or disjointness assumptions. -/
noncomputable def toHullFactorData
    (d : CanonicalFactorEstimates κ A R S) :
    HullFactorData κ A (R + 1) (S + 1) where
  componentCount := canonicalInteriorCount R S A
  boundary := canonicalBoundary R S A
  interior := canonicalInterior R S A
  partition := canonical_partition R S A
  boundary_disjoint := canonicalBoundary_disjoint_interiorUnion R S A
  interior_pairwise := canonicalInterior_pairwise R S A
  componentProduct := d.componentProduct
  boundaryFactor := d.boundaryFactor
  interiorFactor := d.interiorFactor

end CanonicalFactorEstimates

/-- Canonical estimates for every nondegenerate normalized hull suffice for
the componentwise hull input used by the end-to-end theorem. -/
def CanonicalHullInputs (κ : ℝ) : Prop :=
  ∀ {A : Finset Point} {R S : ℕ},
    1 ≤ R → 1 ≤ S →
      (inducedGrid A).Connected → IsRectHull A 0 0 (R + 1) (S + 1) →
      Nonempty (CanonicalFactorEstimates κ A R S)

theorem componentwiseHullInputs_of_canonical
    {κ : ℝ} (h : CanonicalHullInputs κ) : ComponentwiseHullInputs κ := by
  intro A r s hconn hHull hr hs
  obtain ⟨R, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0)
  obtain ⟨S, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : s ≠ 0)
  rcases h (by omega) (by omega) hconn hHull with ⟨d⟩
  exact ⟨d.toHullFactorData⟩

end Boundary
end SquareMaximality
