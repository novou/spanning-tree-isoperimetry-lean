import SquareMaximality.Dual.PlanarMinorConstruction

/-!
# Canonical instances of vacancy deletion

This module packages the coordinate and connectivity facts needed to apply
the generic planar deletion/contraction equivalence to the whole vacancy set,
the boundary-attached component, and every interior component.
-/

set_option autoImplicit false

namespace SquareMaximality
namespace Dual

noncomputable section

/-! ## Deleted vertices in the two coordinate models -/

/-- The explicit primal vacancy set is exactly the inverse image, under
natural-coordinate inclusion, of the integer points missing from `A`. -/
theorem mem_encodedPrimalVacancies_iff_not_mem
    {R S : ℕ} {A : Finset Point}
    (p : Fin (R + 1) × Fin (S + 1)) :
    p ∈ encodedPrimalVacancies R S A ↔
      Boundary.ofNatPoint (finPoint p) ∉ A := by
  rw [mem_encodedPrimalVacancies, Boundary.mem_encodedVacancies]
  simp only [finPoint]
  constructor
  · exact fun h ↦ h.2.2
  · intro hp
    exact ⟨Nat.le_of_lt_succ p.1.2, Nat.le_of_lt_succ p.2.2, hp⟩

/-- Boundary-component vertices agree exactly in `Fin` and integer
coordinates. -/
theorem mem_canonicalBoundaryPrimal_iff_mem
    {R S : ℕ} {A : Finset Point}
    (p : Fin (R + 1) × Fin (S + 1)) :
    p ∈ canonicalBoundaryPrimal R S A ↔
      Boundary.ofNatPoint (finPoint p) ∈
        Boundary.canonicalBoundary R S A := by
  classical
  rw [mem_canonicalBoundaryPrimal]
  simp only [Boundary.canonicalBoundary, Finset.mem_image]
  constructor
  · intro hp
    exact ⟨finPoint p, hp, rfl⟩
  · rintro ⟨z, hz, hzp⟩
    have hzEq : z = finPoint p :=
      Boundary.ofNatPoint_injective (hzp.trans rfl)
    exact hzEq ▸ hz

/-- Interior-component vertices agree exactly in `Fin` and integer
coordinates. -/
theorem mem_canonicalInteriorPrimal_iff_mem
    {R S : ℕ} {A : Finset Point}
    (i : Fin (Boundary.canonicalInteriorCount R S A))
    (p : Fin (R + 1) × Fin (S + 1)) :
    p ∈ canonicalInteriorPrimal R S A i ↔
      Boundary.ofNatPoint (finPoint p) ∈
        Boundary.canonicalInterior R S A i := by
  classical
  rw [mem_canonicalInteriorPrimal]
  simp only [Boundary.canonicalInterior, Finset.mem_image]
  constructor
  · intro hp
    exact ⟨finPoint p, hp, rfl⟩
  · rintro ⟨z, hz, hzp⟩
    have hzEq : z = finPoint p :=
      Boundary.ofNatPoint_injective (hzp.trans rfl)
    exact hzEq ▸ hz

/-- Coordinate data saying that `X` is exactly the set of explicit primal
vertices deleted from the retained integer-coordinate set `D`. -/
structure VacancyDeletionCoordinateData
    (R S : ℕ)
    (X : Finset (Fin (R + 1) × Fin (S + 1)))
    (D : Finset Point) : Prop where
  retained_subset : D ⊆ rectangle 0 0 (R + 1) (S + 1)
  deleted_iff : ∀ p,
    p ∈ X ↔ Boundary.ofNatPoint (finPoint p) ∉ D

private theorem ofNatPoint_finPoint_mem_rectangle
    {R S : ℕ} (p : Fin (R + 1) × Fin (S + 1)) :
    Boundary.ofNatPoint (finPoint p) ∈
      rectangle 0 0 (R + 1) (S + 1) := by
  rw [Boundary.ofNatPoint_mem_standardRectangle]
  exact ⟨Nat.le_of_lt_succ p.1.2, Nat.le_of_lt_succ p.2.2⟩

/-- Coordinate data for deleting every vacancy of `A`. -/
theorem wholeVacancyDeletionCoordinateData
    {R S : ℕ} {A : Finset Point}
    (hHull : IsRectHull A 0 0 (R + 1) (S + 1)) :
    VacancyDeletionCoordinateData R S
      (encodedPrimalVacancies R S A) A where
  retained_subset _ hp := hHull.2.2.1 hp
  deleted_iff := mem_encodedPrimalVacancies_iff_not_mem

/-- Coordinate data for deleting the boundary-attached component. -/
theorem boundaryVacancyDeletionCoordinateData
    (R S : ℕ) (A : Finset Point) :
    VacancyDeletionCoordinateData R S
      (canonicalBoundaryPrimal R S A)
      (rectangle 0 0 (R + 1) (S + 1) \
        Boundary.canonicalBoundary R S A) where
  retained_subset _ hp := (Finset.mem_sdiff.mp hp).1
  deleted_iff p := by
    rw [mem_canonicalBoundaryPrimal_iff_mem]
    have hpRect := ofNatPoint_finPoint_mem_rectangle (R := R) (S := S) p
    simp only [Finset.mem_sdiff, hpRect, true_and, not_not]

/-- Coordinate data for deleting one canonical interior component. -/
theorem interiorVacancyDeletionCoordinateData
    (R S : ℕ) (A : Finset Point)
    (i : Fin (Boundary.canonicalInteriorCount R S A)) :
    VacancyDeletionCoordinateData R S
      (canonicalInteriorPrimal R S A i)
      (rectangle 0 0 (R + 1) (S + 1) \
        Boundary.canonicalInterior R S A i) where
  retained_subset _ hp := (Finset.mem_sdiff.mp hp).1
  deleted_iff p := by
    rw [mem_canonicalInteriorPrimal_iff_mem]
    have hpRect := ofNatPoint_finPoint_mem_rectangle (R := R) (S := S) p
    simp only [Finset.mem_sdiff, hpRect, true_and, not_not]

/-! ## Connectivity of all three retained graphs -/

/-- Deleting all encoded vacancies leaves exactly the original connected
set `A`; this alias records the connectivity input in the same shape as the
other two canonical cases. -/
theorem wholeVacancyDeletion_connected
    {A : Finset Point}
    (hconn : (inducedGrid A).Connected) :
    (inducedGrid A).Connected :=
  hconn

/-- Deleting the boundary-attached vacancy component leaves a connected
grid. -/
theorem boundaryVacancyDeletion_connected
    {R S : ℕ} {A : Finset Point}
    (hHull : IsRectHull A 0 0 (R + 1) (S + 1))
    (hconn : (inducedGrid A).Connected) :
    (inducedGrid (rectangle 0 0 (R + 1) (S + 1) \
      Boundary.canonicalBoundary R S A)).Connected :=
  canonicalBoundaryDeletedGrid_connected hHull hconn

/-- Deleting any one canonical interior component leaves a connected grid. -/
theorem interiorVacancyDeletion_connected
    {R S : ℕ} {A : Finset Point}
    (hHull : IsRectHull A 0 0 (R + 1) (S + 1))
    (hconn : (inducedGrid A).Connected)
    (i : Fin (Boundary.canonicalInteriorCount R S A)) :
    (inducedGrid (rectangle 0 0 (R + 1) (S + 1) \
      Boundary.canonicalInterior R S A i)).Connected :=
  interiorDeletionConnected_of_hull hHull hconn i

/-! ## Generic minor construction in the three canonical cases -/

/-- Coordinate data plus retained-grid connectivity give the exact
deletion/contraction tree equivalence. -/
noncomputable def VacancyDeletionCoordinateData.treeEquiv
    {R S : ℕ} (hR : 1 ≤ R) (hS : 1 ≤ S)
    {X : Finset (Fin (R + 1) × Fin (S + 1))}
    {D : Finset Point}
    (d : VacancyDeletionCoordinateData R S X D)
    (hconn : (inducedGrid D).Connected) :
    VacancyDeletionTreeEquiv R S X D :=
  vacancyDeletionTreeEquivOfCoordinateData
    hR hS d.retained_subset d.deleted_iff hconn

/-- Whole-vacancy deletion/contraction duality, with no planar-minor input. -/
noncomputable def wholeVacancyDeletionTreeEquiv
    {R S : ℕ} (hR : 1 ≤ R) (hS : 1 ≤ S)
    {A : Finset Point}
    (hHull : IsRectHull A 0 0 (R + 1) (S + 1))
    (hconn : (inducedGrid A).Connected) :
    VacancyDeletionTreeEquiv R S
      (encodedPrimalVacancies R S A) A :=
  (wholeVacancyDeletionCoordinateData hHull).treeEquiv hR hS hconn

/-- Boundary-vacancy deletion/contraction duality from the generic minor
construction. -/
noncomputable def boundaryVacancyDeletionTreeEquivOfMinor
    {R S : ℕ} (hR : 1 ≤ R) (hS : 1 ≤ S)
    {A : Finset Point}
    (hHull : IsRectHull A 0 0 (R + 1) (S + 1))
    (hconn : (inducedGrid A).Connected) :
    VacancyDeletionTreeEquiv R S
      (canonicalBoundaryPrimal R S A)
      (rectangle 0 0 (R + 1) (S + 1) \
        Boundary.canonicalBoundary R S A) :=
  (boundaryVacancyDeletionCoordinateData R S A).treeEquiv hR hS
    (boundaryVacancyDeletion_connected hHull hconn)

/-- Interior-component deletion/contraction duality, with no planar-minor
input. -/
noncomputable def interiorVacancyDeletionTreeEquiv
    {R S : ℕ} (hR : 1 ≤ R) (hS : 1 ≤ S)
    {A : Finset Point}
    (hHull : IsRectHull A 0 0 (R + 1) (S + 1))
    (hconn : (inducedGrid A).Connected)
    (i : Fin (Boundary.canonicalInteriorCount R S A)) :
    VacancyDeletionTreeEquiv R S
      (canonicalInteriorPrimal R S A i)
      (rectangle 0 0 (R + 1) (S + 1) \
        Boundary.canonicalInterior R S A i) :=
  (interiorVacancyDeletionCoordinateData R S A i).treeEquiv hR hS
    (interiorVacancyDeletion_connected hHull hconn i)

/-- The complete canonical whole/boundary/interior deletion family. -/
noncomputable def canonicalVacancyDeletionTreeEquivs
    {R S : ℕ} (hR : 1 ≤ R) (hS : 1 ≤ S)
    {A : Finset Point}
    (hHull : IsRectHull A 0 0 (R + 1) (S + 1))
    (hconn : (inducedGrid A).Connected) :
    CanonicalVacancyDeletionTreeEquivs A R S where
  whole := wholeVacancyDeletionTreeEquiv hR hS hHull hconn
  boundary := boundaryVacancyDeletionTreeEquivOfMinor
    hR hS hHull hconn
  interior := interiorVacancyDeletionTreeEquiv hR hS hHull hconn

/-! ## Already-complete boundary equivalence -/

/-- The unconditional explicit boundary cotree construction, restated in
the common `VacancyDeletionTreeEquiv` interface used by forest events. -/
noncomputable def canonicalBoundaryVacancyDeletionTreeEquiv
    {R S : ℕ} (hR : 1 ≤ R) (hS : 1 ≤ S)
    {A : Finset Point}
    (hHull : IsRectHull A 0 0 (R + 1) (S + 1))
    (hconn : (inducedGrid A).Connected) :
    VacancyDeletionTreeEquiv R S
      (canonicalBoundaryPrimal R S A)
      (rectangle 0 0 (R + 1) (S + 1) \
        Boundary.canonicalBoundary R S A) := by
  let G := rectangleDual (R + 1) (S + 1)
  let D := vacancyDualEdges (canonicalBoundaryPrimal R S A)
  exact (boundaryVacancyTreeEquivOfComplementLawStandard R S A
    (canonicalBoundaryVacancyTreeComplementLaw hR hS hHull hconn)).trans
      (spanningTreeEquivOfFintype (G.contract D)
        (G.contractionComponentFintype D) inferInstance)

/-- Assemble the consolidated canonical family once the generic planar-minor
construction has supplied the whole and interior equivalences.  The boundary
field is already unconditional. -/
noncomputable def canonicalVacancyDeletionTreeEquivsOfWholeInterior
    {R S : ℕ} (hR : 1 ≤ R) (hS : 1 ≤ S)
    {A : Finset Point}
    (hHull : IsRectHull A 0 0 (R + 1) (S + 1))
    (hconn : (inducedGrid A).Connected)
    (hWhole : VacancyDeletionTreeEquiv R S
      (encodedPrimalVacancies R S A) A)
    (hInterior : ∀ i, VacancyDeletionTreeEquiv R S
      (canonicalInteriorPrimal R S A i)
      (rectangle 0 0 (R + 1) (S + 1) \
        Boundary.canonicalInterior R S A i)) :
    CanonicalVacancyDeletionTreeEquivs A R S where
  whole := hWhole
  boundary := canonicalBoundaryVacancyDeletionTreeEquiv
    hR hS hHull hconn
  interior := hInterior

/-- Completion-facing forest events from the two still-generic planar-minor
families. -/
noncomputable def canonicalForestEventsOfWholeInteriorDeletion
    {R S : ℕ} (hR : 1 ≤ R) (hS : 1 ≤ S)
    {A : Finset Point}
    (hHull : IsRectHull A 0 0 (R + 1) (S + 1))
    (hconn : (inducedGrid A).Connected)
    (hWhole : VacancyDeletionTreeEquiv R S
      (encodedPrimalVacancies R S A) A)
    (hInterior : ∀ i, VacancyDeletionTreeEquiv R S
      (canonicalInteriorPrimal R S A i)
      (rectangle 0 0 (R + 1) (S + 1) \
        Boundary.canonicalInterior R S A i)) :
    CanonicalForestEvents A R S :=
  (canonicalVacancyDeletionTreeEquivsOfWholeInterior
    hR hS hHull hconn hWhole hInterior).canonicalForestEvents hR hS

/-- Completion-facing interior planar-duality inputs from the same interior
deletion family. -/
theorem interiorPlanarDualityOfInteriorDeletion
    {R S : ℕ} (hR : 1 ≤ R) (hS : 1 ≤ S)
    {A : Finset Point}
    (hInterior : ∀ i, VacancyDeletionTreeEquiv R S
      (canonicalInteriorPrimal R S A i)
      (rectangle 0 0 (R + 1) (S + 1) \
        Boundary.canonicalInterior R S A i))
    (i : Fin (Boundary.canonicalInteriorCount R S A)) :
    InteriorPlanarDualityInput A R S i :=
  interiorPlanarDualityInputOfVacancyDeletionTreeEquiv
    R S A hR hS i (hInterior i)

end


end Dual
end SquareMaximality
